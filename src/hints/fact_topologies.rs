use cairo_vm::types::builtin_name::BuiltinName;
use std::fs::File;
use std::path::Path;

use cairo_vm::types::errors::math_errors::MathError;
use cairo_vm::types::relocatable::Relocatable;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use cairo_vm::vm::runners::builtin_runner::{OutputBuiltinRunner, OutputBuiltinState};
use cairo_vm::vm::runners::cairo_pie::{
    BuiltinAdditionalData, OutputBuiltinAdditionalData, Pages, PublicMemoryPage,
};
use serde::Serialize;

use crate::hints::types::{PackedOutput, Task};

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct FactTopology {
    #[allow(dead_code)]
    pub tree_structure: Vec<usize>,
    pub page_sizes: Vec<usize>,
}

#[derive(Serialize)]
struct FactTopologyFile<'a> {
    fact_topologies: Vec<&'a FactTopology>,
}

impl AsRef<FactTopology> for FactTopology {
    fn as_ref(&self) -> &FactTopology {
        self
    }
}

#[derive(thiserror_no_std::Error, Debug)]
pub enum PageError {
    #[error("Expected page ID {0}, found {1}")]
    UnexpectedPageId(usize, usize),

    #[error("Invalid page start: {0}")]
    InvalidPageStart(usize),

    #[error("Expected page start {0}, found {1}")]
    UnexpectedPageStart(usize, usize),

    #[error("Pages must cover the entire program output")]
    OutputNotFullyCovered,
}

#[derive(thiserror_no_std::Error, Debug)]
pub enum TreeStructureError {
    #[error("Invalid tree structure specified in the gps_fact_topology attribute")]
    InvalidTreeStructure,

    #[error(
        "Additional pages cannot be used since the gps_fact_topology attribute is not specified"
    )]
    CannotUseAdditionalPages,
}

#[derive(Debug, thiserror_no_std::Error)]
pub enum FactTopologyError {
    #[error(transparent)]
    Math(#[from] MathError),

    #[error(transparent)]
    PageSize(#[from] PageError),

    #[error(transparent)]
    TreeStructure(#[from] TreeStructureError),

    #[error("Expected {0} fact topologies but got {1}")]
    WrongNumberOfFactTopologies(usize, usize),

    #[error("Composite packed outputs are not supported yet")]
    CompositePackedOutputNotSupported(PackedOutput),

    #[error("Could not add page to output: {0}")]
    FailedToAddOutputPage(#[from] RunnerError),

    #[error("Could not load output builtin additional data from Cairo PIE")]
    CairoPieHasNoOutputBuiltinData,

    #[error("Unexpected error: {0}")]
    Internal(Box<str>),
}

impl From<FactTopologyError> for HintError {
    fn from(value: FactTopologyError) -> Self {
        match value {
            FactTopologyError::Math(e) => HintError::Math(e),
            FactTopologyError::WrongNumberOfFactTopologies(_, _) => {
                HintError::AssertionFailed(value.to_string().into_boxed_str())
            }
            _ => HintError::CustomHint(value.to_string().into_boxed_str()),
        }
    }
}

#[derive(thiserror_no_std::Error, Debug)]
pub enum WriteFactTopologiesError {
    #[error("Failed to create fact topology file: {0}")]
    Io(#[from] std::io::Error),
    #[error("Failed to serialize fact topologies: {0}")]
    Serialization(#[from] serde_json::Error),
}

impl From<WriteFactTopologiesError> for HintError {
    fn from(value: WriteFactTopologiesError) -> Self {
        HintError::CustomHint(value.to_string().into_boxed_str())
    }
}

/// Flattens and extracts the fact topologies from packed outputs.
///
/// Note that `packed_outputs` and `fact_topologies` must have the same length.
///
/// * `packed_outputs`: Packed outputs.
/// * `fact_topologies`: Fact topologies.
pub fn compute_fact_topologies<'a>(
    packed_outputs: &Vec<PackedOutput>,
    fact_topologies: &'a Vec<FactTopology>,
) -> Result<Vec<&'a FactTopology>, FactTopologyError> {
    if packed_outputs.len() != fact_topologies.len() {
        return Err(FactTopologyError::WrongNumberOfFactTopologies(
            packed_outputs.len(),
            fact_topologies.len(),
        ));
    }

    let mut plain_fact_topologies = vec![];

    for (packed_output, fact_topology) in std::iter::zip(packed_outputs, fact_topologies) {
        match packed_output {
            PackedOutput::Plain(_) => {
                plain_fact_topologies.push(fact_topology);
            }
            PackedOutput::Composite(_) => {
                return Err(FactTopologyError::CompositePackedOutputNotSupported(
                    packed_output.clone(),
                ));
            }
        }
    }

    Ok(plain_fact_topologies)
}

/// Adds page to the output builtin for the specified fact topology.
///
/// * `fact_topology`: Fact topology.
/// * `output_builtin`: Output builtin of the VM.
/// * `current_page_id`: First page ID to use.
/// * `output_start`: Start of the output range for this fact topology.
///
/// Reimplements the following Python code:
///     offset = 0
///     for i, page_size in enumerate(fact_topology.page_sizes):
///         output_builtin.add_page(
///             page_id=cur_page_id + i, page_start=output_start + offset, page_size=page_size
///         )
///         offset += page_size
///
///     return len(fact_topology.page_sizes)
fn add_consecutive_output_pages(
    fact_topology: &FactTopology,
    output_builtin: &mut OutputBuiltinRunner,
    current_page_id: usize,
    output_start: Relocatable,
) -> Result<usize, FactTopologyError> {
    let mut offset = 0;

    for (i, page_size) in fact_topology.page_sizes.iter().copied().enumerate() {
        let page_id = current_page_id + i;
        let page_start = (output_start + offset)?;
        output_builtin.add_page(page_id, page_start, page_size)?;
        offset += page_size;
    }

    Ok(fact_topology.page_sizes.len())
}

/// Given the fact_topologies of the tasks that were run by bootloader, configure the
/// corresponding pages in the output builtin.
///
/// Assumes that the bootloader output 2 words per task.
///
/// * `plain_fact_topologies`: Fact topologies.
/// * `output_start`: Start of the bootloader output.
/// * `output_builtin`: Output builtin of the VM.
///
/// Reimplements the following Python code:
/// cur_page_id = 1
/// for fact_topology in fact_topologies:
///     # Skip bootloader output for each task.
///     output_start += 2
///     cur_page_id += add_consecutive_output_pages(
///         fact_topology=fact_topology,
///         output_builtin=output_builtin,
///         cur_page_id=cur_page_id,
///         output_start=output_start,
///     )
///     output_start += sum(fact_topology.page_sizes)

pub fn configure_fact_topologies<FT: AsRef<FactTopology>>(
    plain_fact_topologies: &[FT],
    output_start: &mut Relocatable,
    output_builtin: &mut OutputBuiltinRunner,
) -> Result<(), FactTopologyError> {
    // Each task may use a few memory pages. Start from page 1 (as page 0 is reserved for the
    // bootloader program and arguments).
    let mut current_page_id: usize = 1;
    for fact_topology in plain_fact_topologies {
        // Skip bootloader output for each task
        *output_start = (*output_start + 2usize)?;

        current_page_id += add_consecutive_output_pages(
            fact_topology.as_ref(),
            output_builtin,
            current_page_id,
            *output_start,
        )?;
        let total_page_sizes: usize = fact_topology.as_ref().page_sizes.iter().sum();
        *output_start = (*output_start + total_page_sizes)?;
    }

    Ok(())
}

fn check_tree_structure(tree_structure: &[usize]) -> Result<(), TreeStructureError> {
    if (!tree_structure.len().is_power_of_two()) || (tree_structure.len() > 10) {
        return Err(TreeStructureError::InvalidTreeStructure);
    }

    let max_element_size: usize = 1 << 30;
    for x in tree_structure {
        if *x > max_element_size {
            return Err(TreeStructureError::InvalidTreeStructure);
        }
    }

    Ok(())
}

const GPS_FACT_TOPOLOGY: &str = "gps_fact_topology";

/// Extracts the tree structure from the output data attributes, or returns a default.
fn get_tree_structure_from_output_data(
    output_builtin_additional_data: &OutputBuiltinAdditionalData,
) -> Result<Vec<usize>, TreeStructureError> {
    let pages = &output_builtin_additional_data.pages;
    let attributes = &output_builtin_additional_data.attributes;

    // If the GPS_FACT_TOPOLOGY attribute is present, use it. Otherwise, the task is expected to
    // use exactly one page (page 0).
    let tree_structure = match attributes.get(GPS_FACT_TOPOLOGY) {
        Some(tree_structure_attr) => {
            check_tree_structure(tree_structure_attr)?;
            tree_structure_attr.clone()
        }
        None => {
            if !pages.is_empty() {
                return Err(TreeStructureError::CannotUseAdditionalPages);
            }
            vec![1, 0]
        }
    };

    Ok(tree_structure)
}

/// Returns the sizes of the program output pages, given the pages that appears
/// in the additional attributes of the output builtin.
fn get_page_sizes_from_pages(output_size: usize, pages: &Pages) -> Result<Vec<usize>, PageError> {
    // Make sure the pages are adjacent to each other.

    // The first page id is expected to be 1.
    let mut expected_page_id: usize = 1;
    // We don't expect anything on its start value.
    let mut expected_page_start: usize = 0;
    // The size of page 0 is output_size if there are no other pages, or the start of page 1
    // otherwise.
    let mut page0_size = output_size;

    let mut page_sizes: Vec<usize> = vec![0; pages.len() + 1];

    let sorted_pages_vec = {
        let mut v: Vec<(&usize, &PublicMemoryPage)> = pages.iter().collect();
        v.sort_by_key(|x| x.0);
        v
    };

    for (index, (page_id, page)) in sorted_pages_vec.iter().cloned().enumerate() {
        if *page_id != expected_page_id {
            return Err(PageError::UnexpectedPageId(expected_page_id, *page_id));
        }

        if *page_id == 1 {
            if page.start > output_size {
                return Err(PageError::InvalidPageStart(page.start));
            }
            page0_size = page.start;
        } else if page.start != expected_page_start {
            return Err(PageError::UnexpectedPageStart(
                expected_page_start,
                page.start,
            ));
        }

        page_sizes[index + 1] = page.size;
        expected_page_start = page.start + page.size;
        expected_page_id += 1;
    }

    if !pages.is_empty() {
        // The loop above did not cover the whole output range
        if expected_page_start != output_size {
            return Err(PageError::OutputNotFullyCovered);
        }
    }

    page_sizes[0] = page0_size;
    Ok(page_sizes)
}

fn get_fact_topology_from_additional_data(
    output_size: usize,
    output_builtin_additional_data: &OutputBuiltinAdditionalData,
) -> Result<FactTopology, FactTopologyError> {
    let tree_structure = get_tree_structure_from_output_data(output_builtin_additional_data)?;
    let page_sizes = get_page_sizes_from_pages(output_size, &output_builtin_additional_data.pages)?;

    Ok(FactTopology {
        tree_structure,
        page_sizes,
    })
}

// TODO: implement for CairoPieTask
fn get_program_task_fact_topology(
    output_size: usize,
    output_builtin: &mut OutputBuiltinRunner,
    output_runner_data: OutputBuiltinState,
) -> Result<FactTopology, FactTopologyError> {
    let additional_data = match output_builtin.get_additional_data() {
        BuiltinAdditionalData::Output(data) => data,
        other => {
            return Err(FactTopologyError::Internal(
                format!(
                    "Additional data of output builtin is not of the expected type: {:?}",
                    other
                )
                .into_boxed_str(),
            ))
        }
    };
    let fact_topology = get_fact_topology_from_additional_data(output_size, &additional_data)?;
    output_builtin.set_state(output_runner_data);

    Ok(fact_topology)
}

pub fn get_task_fact_topology(
    output_size: usize,
    task: &Task,
    output_builtin: &mut OutputBuiltinRunner,
    output_runner_data: Option<OutputBuiltinState>,
) -> Result<FactTopology, FactTopologyError> {
    match task {
        Task::Program(_program) => {
            let output_runner_data = output_runner_data.ok_or(FactTopologyError::Internal(
                "Output runner data not set for program task"
                    .to_string()
                    .into_boxed_str(),
            ))?;
            get_program_task_fact_topology(output_size, output_builtin, output_runner_data)
        }
        Task::Pie(cairo_pie) => {
            if output_runner_data.is_some() {
                return Err(FactTopologyError::Internal(
                    "Output runner data set for Cairo PIE task"
                        .to_string()
                        .into_boxed_str(),
                ));
            }
            let additional_data = {
                let additional_data = cairo_pie
                    .additional_data
                    .0
                    .get(&BuiltinName::output)
                    .ok_or(FactTopologyError::CairoPieHasNoOutputBuiltinData)?;
                match additional_data {
                    BuiltinAdditionalData::Output(output_data) => output_data,
                    _ => {
                        return Err(FactTopologyError::CairoPieHasNoOutputBuiltinData);
                    }
                }
            };

            get_fact_topology_from_additional_data(output_size, additional_data)
        }
    }
}

/// Writes fact topologies to a file, as JSON.
///
/// * `path`: File path.
/// * `fact_topologies`: Fact topologies to write.
pub fn write_to_fact_topologies_file<FT: AsRef<FactTopology>>(
    path: &Path,
    fact_topologies: &[FT],
) -> Result<(), WriteFactTopologiesError> {
    let mut file = File::create(path)?;
    let fact_topology_file = FactTopologyFile {
        fact_topologies: fact_topologies.iter().map(|ft| ft.as_ref()).collect(),
    };
    serde_json::to_writer(&mut file, &fact_topology_file)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::hints::types::CompositePackedOutput;
    use rstest::{fixture, rstest};

    use super::*;

    #[fixture]
    fn packed_outputs() -> Vec<PackedOutput> {
        vec![
            PackedOutput::Plain(vec![]),
            PackedOutput::Plain(vec![]),
            PackedOutput::Plain(vec![]),
        ]
    }

    #[fixture]
    fn fact_topologies() -> Vec<FactTopology> {
        vec![
            FactTopology {
                tree_structure: vec![],
                page_sizes: vec![1usize],
            },
            FactTopology {
                tree_structure: vec![],
                page_sizes: vec![1usize, 2usize],
            },
            FactTopology {
                tree_structure: vec![],
                page_sizes: vec![3usize],
            },
        ]
    }

    #[rstest]
    fn test_compute_fact_topologies(
        packed_outputs: Vec<PackedOutput>,
        fact_topologies: Vec<FactTopology>,
    ) {
        let plain_fact_topologies = compute_fact_topologies(&packed_outputs, &fact_topologies)
            .expect("Failed to compute fact topologies");
        for (topology, plain_topology) in std::iter::zip(&fact_topologies, plain_fact_topologies) {
            assert_eq!(topology, plain_topology);
        }
    }

    #[test]
    /// Composite outputs are not supported (yet).
    fn test_compute_fact_topologies_composite_output() {
        let packed_outputs = vec![PackedOutput::Composite(CompositePackedOutput::default())];
        let fact_topologies = vec![FactTopology {
            tree_structure: vec![],
            page_sizes: vec![],
        }];
        let result = compute_fact_topologies(&packed_outputs, &fact_topologies);
        assert!(matches!(
            result,
            Err(FactTopologyError::CompositePackedOutputNotSupported(_))
        ));
    }

    #[test]
    /// Both arguments to `compute_fact_topologies` must have the same length.
    fn test_compute_fact_topologies_arg_len_mismatch() {
        let packed_outputs = vec![PackedOutput::Plain(vec![])];
        let fact_topologies = vec![];

        let result = compute_fact_topologies(&packed_outputs, &fact_topologies);
        assert!(
            matches!(result, Err(FactTopologyError::WrongNumberOfFactTopologies(n_outputs, n_topologies)) if n_outputs == packed_outputs.len() && n_topologies == fact_topologies.len())
        )
    }

    #[rstest]
    fn test_add_consecutive_output_pages() {
        let fact_topology = FactTopology {
            tree_structure: vec![],
            page_sizes: vec![1usize, 2usize, 1usize],
        };
        let mut output_builtin = OutputBuiltinRunner::new(true);
        let page_id = 1;
        let output_start = Relocatable {
            segment_index: 0,
            offset: 10,
        };

        let result = add_consecutive_output_pages(
            &fact_topology,
            &mut output_builtin,
            page_id,
            output_start,
        )
        .expect("Adding consecutive output pages failed unexpectedly");
        assert_eq!(result, fact_topology.page_sizes.len());

        let output_builtin_state = output_builtin.get_state();
        assert_eq!(
            output_builtin_state.pages,
            HashMap::from([
                (1, PublicMemoryPage { start: 10, size: 1 }),
                (2, PublicMemoryPage { start: 11, size: 2 }),
                (3, PublicMemoryPage { start: 13, size: 1 })
            ])
        );
    }

    #[rstest]
    fn test_configure_fact_topologies(fact_topologies: Vec<FactTopology>) {
        let mut output_builtin = OutputBuiltinRunner::new(true);
        let mut output_start = Relocatable {
            segment_index: output_builtin.base() as isize,
            offset: 10,
        };

        let result =
            configure_fact_topologies(&fact_topologies, &mut output_start, &mut output_builtin)
                .expect("Configuring fact topologies failed unexpectedly");

        assert_eq!(result, ());

        // We expect the offset to 2 + sum(page_sizes) for each fact topology
        let expected_offset: usize = fact_topologies.iter().flat_map(|ft| &ft.page_sizes).sum();
        let expected_offset = expected_offset + fact_topologies.len() * 2;
        assert_eq!(output_start.segment_index, output_builtin.base() as isize);
        assert_eq!(output_start.offset, 10 + expected_offset);

        let output_builtin_state = output_builtin.get_state();
        assert_eq!(
            output_builtin_state.pages,
            HashMap::from([
                (1, PublicMemoryPage { start: 12, size: 1 }),
                (2, PublicMemoryPage { start: 15, size: 1 }),
                (3, PublicMemoryPage { start: 16, size: 2 }),
                (4, PublicMemoryPage { start: 20, size: 3 })
            ])
        );
    }

    #[test]
    fn test_get_tree_structure() {
        let expected_tree_structure = vec![7, 12, 4, 0];

        let output_builtin_data = OutputBuiltinAdditionalData {
            pages: HashMap::new(),
            attributes: HashMap::from([(
                GPS_FACT_TOPOLOGY.to_string(),
                expected_tree_structure.clone(),
            )]),
        };

        let tree_structure = get_tree_structure_from_output_data(&output_builtin_data)
            .expect("Failed to get tree structure");
        assert_eq!(tree_structure, expected_tree_structure);
    }

    #[test]
    fn test_get_tree_structure_default() {
        let output_builtin_data = OutputBuiltinAdditionalData {
            pages: HashMap::new(),
            attributes: HashMap::new(),
        };

        let tree_structure = get_tree_structure_from_output_data(&output_builtin_data)
            .expect("Failed to get tree structure");
        assert_eq!(tree_structure, vec![1, 0]);
    }

    #[rstest]
    #[case::uneven_tree(vec![1, 3, 7])]
    #[case::tree_too_long(vec![1; 12])]
    #[case::value_too_large(vec![0, 1073741825])] // 1073741825 = 2^30 + 1
    fn test_get_tree_structure_invalid_tree(#[case] tree_structure: Vec<usize>) {
        let output_builtin_data = OutputBuiltinAdditionalData {
            pages: HashMap::new(),
            attributes: HashMap::from([(GPS_FACT_TOPOLOGY.to_string(), tree_structure.clone())]),
        };

        let result = get_tree_structure_from_output_data(&output_builtin_data);
        assert!(matches!(
            result,
            Err(TreeStructureError::InvalidTreeStructure)
        ));
    }

    #[test]
    fn test_get_tree_structure_default_with_pages() {
        let output_builtin_data = OutputBuiltinAdditionalData {
            pages: HashMap::from([(1, PublicMemoryPage { start: 0, size: 10 })]),
            attributes: HashMap::new(),
        };

        let result = get_tree_structure_from_output_data(&output_builtin_data);
        assert!(matches!(
            result,
            Err(TreeStructureError::CannotUseAdditionalPages)
        ));
    }

    #[test]
    fn test_get_page_sizes_from_pages() {
        let output_size = 10usize;
        let pages = HashMap::from([
            (1, PublicMemoryPage { start: 0, size: 7 }),
            (2, PublicMemoryPage { start: 7, size: 3 }),
        ]);

        let page_sizes =
            get_page_sizes_from_pages(output_size, &pages).expect("Could not compute page sizes");
        assert_eq!(page_sizes, vec![0, 7, 3]);
    }

    #[test]
    fn test_get_page_sizes_missing() {
        let output_size = 10usize;
        let page_sizes = get_page_sizes_from_pages(output_size, &HashMap::new())
            .expect("Could not compute page sizes");
        assert_eq!(page_sizes, vec![output_size]);
    }

    #[test]
    fn test_get_page_sizes_unexpected_page_id() {
        let output_size = 10usize;
        let pages = HashMap::from([
            (1, PublicMemoryPage { start: 0, size: 7 }),
            (3, PublicMemoryPage { start: 7, size: 3 }),
        ]);

        let result = get_page_sizes_from_pages(output_size, &pages);
        assert!(matches!(result, Err(PageError::UnexpectedPageId(2, 3))));
    }

    #[test]
    fn test_get_page_sizes_invalid_page_start() {
        let output_size = 10usize;
        let pages = HashMap::from([
            (1, PublicMemoryPage { start: 12, size: 7 }),
            (2, PublicMemoryPage { start: 19, size: 3 }),
        ]);

        let result = get_page_sizes_from_pages(output_size, &pages);
        assert!(matches!(result, Err(PageError::InvalidPageStart(12))));
    }

    #[test]
    fn test_get_page_sizes_unexpected_page_start() {
        let output_size = 10usize;
        let pages = HashMap::from([
            (1, PublicMemoryPage { start: 0, size: 7 }),
            (2, PublicMemoryPage { start: 8, size: 3 }),
        ]);

        let result = get_page_sizes_from_pages(output_size, &pages);
        assert!(matches!(result, Err(PageError::UnexpectedPageStart(7, 8))));
    }

    #[test]
    fn test_get_page_sizes_output_not_fully_covered() {
        let output_size = 10usize;
        let pages = HashMap::from([
            (1, PublicMemoryPage { start: 0, size: 7 }),
            (2, PublicMemoryPage { start: 7, size: 2 }),
        ]);

        let result = get_page_sizes_from_pages(output_size, &pages);
        assert!(matches!(result, Err(PageError::OutputNotFullyCovered)));
    }
}
