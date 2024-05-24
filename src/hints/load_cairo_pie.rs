use std::collections::HashMap;

use cairo_vm::types::builtin_name::BuiltinName;
use cairo_vm::types::errors::math_errors::MathError;
use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::errors::memory_errors::MemoryError;
use cairo_vm::vm::runners::builtin_runner::SignatureBuiltinRunner;
use cairo_vm::vm::runners::cairo_pie::{BuiltinAdditionalData, CairoPie, CairoPieMemory};
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::Felt252;
use thiserror_no_std::Error;

#[derive(Error, Debug)]
pub enum RelocationTableError {
    #[error(transparent)]
    Math(#[from] MathError),

    #[error(transparent)]
    Memory(#[from] MemoryError),

    #[error("Expected relocatable to point to the start of a segment: {0}")]
    ExpectedSegmentBase(Relocatable),

    #[error("Segment index already present in the relocation table: {0}")]
    SegmentAlreadyMapped(isize),
}

#[derive(Error, Debug)]
pub enum SignatureRelocationError {
    #[error(transparent)]
    Memory(#[from] MemoryError),

    #[error("The PIE requires ECDSA but the VM is not configured to use it")]
    EcdsaBuiltinNotFound,

    #[error("Relocated signature data ({0} not on signature builtin segment {1}")]
    RelocatedDataNotOnBuiltinSegment(Relocatable, isize),

    #[error("The Cairo PIE ECDSA builtin data is not in the expected format")]
    InvalidCairoPieEcdsaBuiltinData,
}

#[derive(Error, Debug)]
pub enum MemoryRelocationError {
    #[error(transparent)]
    Memory(#[from] MemoryError),
}

#[derive(Error, Debug)]
pub enum CairoPieLoaderError {
    #[error("Error while building relocation table: {0}")]
    RelocationTable(#[from] RelocationTableError),

    #[error("Error while relocating signature builtin data: {0}")]
    SignatureRelocation(#[from] SignatureRelocationError),

    #[error("Error while relocating Cairo PIE memory: {0}")]
    MemoryRelocationError(#[from] MemoryRelocationError),
}

impl From<CairoPieLoaderError> for HintError {
    fn from(value: CairoPieLoaderError) -> Self {
        HintError::CustomHint(value.to_string().into_boxed_str())
    }
}

/// Keeps track of relocations for different segments.
///
/// Each entry in `relocations` maps a segment index from the PIE to
/// a pointer in the VM memory.
pub struct RelocationTable {
    relocations: HashMap<isize, Relocatable>,
}

impl RelocationTable {
    pub fn new() -> Self {
        Self {
            relocations: Default::default(),
        }
    }

    /// Inserts an entry in the relocations map.
    ///
    /// * `segment_index`: Index of the Cairo PIE segment.
    /// * `relocation`: Destination in the VM memory.
    ///
    /// Returns `SegmentAlreadyMapped` if a relocation entry already exists for
    /// `segment_index`.
    pub fn insert(
        &mut self,
        segment_index: isize,
        relocation: Relocatable,
    ) -> Result<(), RelocationTableError> {
        if self.relocations.contains_key(&segment_index) {
            return Err(RelocationTableError::SegmentAlreadyMapped(segment_index));
        }
        self.relocations.insert(segment_index, relocation);

        Ok(())
    }

    /// Relocates a pointer.
    ///
    /// Considering a relocatable (i, o), if a relocation table entry i -> (i*, o*) exists,
    /// returns (i*, o + o*).
    /// Returns `MemoryError::Relocation` if there is no matching relocation.
    pub fn relocate_address(&self, address: Relocatable) -> Result<Relocatable, MemoryError> {
        let new_base = self
            .relocations
            .get(&address.segment_index)
            .ok_or(MemoryError::Relocation)?;

        let relocated_pointer = (*new_base + address.offset)?;
        Ok(relocated_pointer)
    }

    /// Relocates any value.
    ///
    /// Returns the value directly if it is an integer, otherwise returns the relocated address
    /// using `relocate_address`.
    pub fn relocate_value(&self, value: MaybeRelocatable) -> Result<MaybeRelocatable, MemoryError> {
        match value {
            MaybeRelocatable::Int(_) => Ok(value),
            MaybeRelocatable::RelocatableValue(address) => {
                let relocated_addr = self.relocate_address(address);
                relocated_addr.map(MaybeRelocatable::RelocatableValue)
            }
        }
    }
}

/// Returns the segment index for the given value.
/// Verifies that value is a RelocatableValue with offset 0.
pub fn extract_segment(maybe_relocatable: MaybeRelocatable) -> Result<isize, RelocationTableError> {
    match maybe_relocatable {
        MaybeRelocatable::RelocatableValue(address) => {
            if address.offset != 0 {
                return Err(RelocationTableError::ExpectedSegmentBase(address));
            }

            Ok(address.segment_index)
        }
        MaybeRelocatable::Int(_) => Err(RelocationTableError::Memory(
            MemoryError::AddressNotRelocatable,
        )),
    }
}

/// Builds a hashmap of address -> value from the `CairoPieMemory` vector.
///
/// Makes it more convenient to access values in the Cairo PIE memory.
fn build_cairo_pie_memory_map(memory: &CairoPieMemory) -> HashMap<Relocatable, &MaybeRelocatable> {
    let mut memory_map: HashMap<Relocatable, &MaybeRelocatable> = HashMap::new();

    for ((segment_index, offset), value) in memory.0.iter() {
        let address = Relocatable::from((*segment_index as isize, *offset));
        memory_map.insert(address, value);
    }

    memory_map
}

/// Builds a relocation table for the specified Cairo PIE.
pub fn build_cairo_pie_relocation_table(
    cairo_pie: &CairoPie,
    vm: &mut VirtualMachine,
    program_address: Relocatable,
    execution_segment_address: Relocatable,
    ret_fp: Relocatable,
    ret_pc: Relocatable,
) -> Result<RelocationTable, RelocationTableError> {
    let mut relocation_table = RelocationTable::new();

    relocation_table.insert(cairo_pie.metadata.program_segment.index, program_address)?;
    relocation_table.insert(
        cairo_pie.metadata.execution_segment.index,
        execution_segment_address,
    )?;
    relocation_table.insert(cairo_pie.metadata.ret_fp_segment.index, ret_fp)?;
    relocation_table.insert(cairo_pie.metadata.ret_pc_segment.index, ret_pc)?;

    let origin_execution_segment = Relocatable {
        segment_index: cairo_pie.metadata.execution_segment.index,
        offset: 0,
    };

    // Create a hashmap of the program memory for easier searching.
    // If this turns out to be too expensive, consider building it directly
    // when building the CairoPie object.
    let memory_map = build_cairo_pie_memory_map(&cairo_pie.memory);

    // Set initial stack relocations.
    for (idx, _builtin_name) in cairo_pie.metadata.program.builtins.iter().enumerate() {
        let memory_address = (origin_execution_segment + idx)?;
        let segment_index = extract_segment(memory_map[&memory_address].clone())?;
        let relocation = vm.get_relocatable((execution_segment_address + idx)?)?;
        relocation_table.insert(segment_index, relocation)?;
    }

    for segment_info in cairo_pie.metadata.extra_segments.iter() {
        relocation_table.insert(segment_info.index, vm.add_memory_segment())?;
    }

    Ok(relocation_table)
}

fn extend_additional_data(
    builtin: &mut SignatureBuiltinRunner,
    data: &HashMap<Relocatable, (Felt252, Felt252)>,
    relocation_table: &RelocationTable,
) -> Result<(), SignatureRelocationError> {
    for (addr, signature) in data {
        let relocated_addr = relocation_table.relocate_address(*addr)?;
        let builtin_segment_base = builtin.base() as isize;
        if relocated_addr.segment_index != builtin_segment_base {
            return Err(SignatureRelocationError::RelocatedDataNotOnBuiltinSegment(
                relocated_addr,
                builtin_segment_base,
            ));
        }
        builtin.add_signature(*addr, signature)?;
    }

    Ok(())
}

/// Relocate builtin additional data.
/// This should occur before the memory relocation, since the signature builtin assumes that a
/// signature is added before the corresponding public key and message are both written to memory.
fn relocate_builtin_additional_data(
    cairo_pie: &CairoPie,
    vm: &mut VirtualMachine,
    relocation_table: &RelocationTable,
) -> Result<(), SignatureRelocationError> {
    let ecdsa_additional_data = match cairo_pie.additional_data.0.get(&BuiltinName::ecdsa) {
        Some(BuiltinAdditionalData::Signature(data)) => data,
        Some(_) => return Err(SignatureRelocationError::InvalidCairoPieEcdsaBuiltinData),
        _ => return Ok(()),
    };

    let ecdsa_builtin = vm
        .get_signature_builtin()
        .map_err(|_| SignatureRelocationError::EcdsaBuiltinNotFound)?;

    extend_additional_data(ecdsa_builtin, ecdsa_additional_data, relocation_table)?;

    Ok(())
}

/// Relocates the memory of the PIE.
///
/// * `cairo_pie`: Cairo PIE.
/// * `vm`: Virtual machine.
/// * `relocation_table`: Relocation rules.
fn relocate_cairo_pie_memory(
    cairo_pie: &CairoPie,
    vm: &mut VirtualMachine,
    relocation_table: &RelocationTable,
) -> Result<(), MemoryRelocationError> {
    // Relocate memory segment
    for ((segment_index, offset), value) in &cairo_pie.memory.0 {
        let address = Relocatable::from((*segment_index as isize, *offset));
        let relocated_address = relocation_table.relocate_address(address)?;
        let relocated_value = relocation_table.relocate_value(value.clone())?;

        vm.insert_value(relocated_address, relocated_value)?;
    }

    Ok(())
}

/// Load memory entries of the inner program.
///
/// Relocates (copies) the memory of the PIE to segments allocated for the current task.
/// This replaces executing hints in a non-trusted program.
pub(crate) fn load_cairo_pie(
    cairo_pie: &CairoPie,
    vm: &mut VirtualMachine,
    program_address: Relocatable,
    execution_segment_address: Relocatable,
    ret_fp: Relocatable,
    ret_pc: Relocatable,
) -> Result<(), CairoPieLoaderError> {
    let relocation_table = build_cairo_pie_relocation_table(
        cairo_pie,
        vm,
        program_address,
        execution_segment_address,
        ret_fp,
        ret_pc,
    )?;

    relocate_builtin_additional_data(cairo_pie, vm, &relocation_table)?;
    relocate_cairo_pie_memory(cairo_pie, vm, &relocation_table)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use super::*;

    #[test]
    fn test_relocate_value() {
        let relocation_table = RelocationTable::new();

        let value = MaybeRelocatable::Int(Felt252::from(64));
        assert_eq!(relocation_table.relocate_value(value.clone()), Ok(value));
    }

    #[test]
    fn test_relocate_address() {
        let mut relocation_table = RelocationTable::new();
        let relocation = Relocatable::from((2, 5));
        relocation_table.insert(1, relocation.clone()).unwrap();

        let address = Relocatable::from((1, 27));
        let expected_address = Relocatable::from((2, 32));
        assert_eq!(
            relocation_table.relocate_address(address),
            Ok(expected_address)
        );

        let value = MaybeRelocatable::RelocatableValue(address);
        let expected_value = MaybeRelocatable::RelocatableValue(expected_address);
        assert_eq!(relocation_table.relocate_value(value), Ok(expected_value));
    }

    #[test]
    fn test_relocate_address_no_matching_relocation() {
        let relocation_table = RelocationTable::new();

        let value = MaybeRelocatable::RelocatableValue(Relocatable::from((1, 0)));
        assert_eq!(
            relocation_table.relocate_value(value.clone()),
            Err(MemoryError::Relocation)
        );
    }

    #[test]
    fn test_relocation_table_write_twice() {
        let segment_index = 1;
        let relocation = Relocatable::from((2, 0));

        let mut relocation_table = RelocationTable::new();
        relocation_table.insert(segment_index, relocation).unwrap();

        let new_relocation = Relocatable::from((3, 0));

        let result = relocation_table.insert(segment_index, new_relocation);
        assert_matches!(
            result,
            Err(RelocationTableError::SegmentAlreadyMapped(idx)) if idx == segment_index
        );
    }

    #[test]
    fn test_extract_segment_base() {
        let address = Relocatable::from((1, 0));
        let result = extract_segment(MaybeRelocatable::RelocatableValue(address)).unwrap();
        assert_eq!(result, address.segment_index);
    }

    #[test]
    fn test_extract_segment_base_not_a_base() {
        let address = Relocatable::from((1, 5));
        let result = extract_segment(MaybeRelocatable::RelocatableValue(address));
        assert_matches!(result, Err(RelocationTableError::ExpectedSegmentBase(relocatable)) if relocatable == address);
    }

    #[test]
    fn test_extract_segment_base_not_an_address() {
        let result = extract_segment(MaybeRelocatable::Int(Felt252::from(1)));
        assert_matches!(
            result,
            Err(RelocationTableError::Memory(
                MemoryError::AddressNotRelocatable
            ))
        );
    }
}
