use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::PathBuf;


#[derive(Serialize, Deserialize, Debug)]
struct StarkFri {
    fri_step_list: Vec<u32>,
    last_layer_degree_bound: u32,
    n_queries: u32,
    proof_of_work_bits: u32,
}

#[derive(Serialize, Deserialize, Debug)]
struct Stark {
    fri: StarkFri,
    log_n_cosets: u32,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Template {
    field: String,
    stark: Stark,
    use_extension_field: bool,
}

impl Template {
    pub fn generate_from_public_input_file(
        file: &PathBuf,
        n_queries: Option<u32>,
        pow_bits: Option<u32>,
    ) -> Self {
        Self::generate_from_public_input(
            ProgramPublicInputAsNSteps::read_from_file(file),
            n_queries,
            pow_bits,
        )
    }
    pub fn save_to_file(&self, file: &PathBuf) -> () {
        let json_string = serde_json::to_string_pretty(self).unwrap();
        File::create(file).unwrap()
            .write_all(json_string.as_bytes())
            .unwrap();
    }
    fn generate_from_public_input(
        public_input: ProgramPublicInputAsNSteps,
        n_queries: Option<u32>,
        pow_bits: Option<u32>,
    ) -> Self {
        let mut template = Self::default();
        if let Some(pow_bits) = pow_bits {
            template.stark.fri.proof_of_work_bits = pow_bits;
        }
        if let Some(n_queries) = n_queries {
            template.stark.fri.n_queries = n_queries;
        }
        let fri_step_list =
            public_input.calculate_fri_step_list(template.stark.fri.last_layer_degree_bound);
        template.stark.fri.fri_step_list = fri_step_list;
        template
    }
}

impl core::default::Default for Template {
    fn default() -> Self {
        Template {
            field: "PrimeField0".to_string(),
            stark: Stark {
                fri: StarkFri {
                    fri_step_list: vec![0, 4, 4, 4],
                    last_layer_degree_bound: 128,
                    n_queries: 16,
                    proof_of_work_bits: 30,
                },
                log_n_cosets: 3,
            },
            use_extension_field: false,
        }
    }
}

#[derive(Debug, Deserialize)]
struct ProgramPublicInputAsNSteps {
    n_steps: u32,
}

impl ProgramPublicInputAsNSteps {
    pub fn read_from_file(input_file: &PathBuf) -> Self {
        serde_json::from_reader(BufReader::new(File::open(input_file).unwrap())).unwrap()
    }
    fn calculate_fri_step_list(&self, degree_bound: u32) -> Vec<u32> {
        let fri_degree = ((self.n_steps as f64 / degree_bound as f64).log(2.0).round() as u32) + 4;
        let mut steps = vec![0];
        steps.extend(vec![4; (fri_degree / 4) as usize]);
        if fri_degree % 4 != 0 {
            steps.push(fri_degree % 4);
        }
        steps
    }
}
