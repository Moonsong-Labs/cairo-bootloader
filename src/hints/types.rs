use std::collections::HashMap;
use std::path::PathBuf;

use cairo_vm::serde::deserialize_program::Identifier;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::program::Program;
use cairo_vm::vm::runners::cairo_pie::{CairoPie, StrippedProgram};
use cairo_vm::Felt252;
use serde::Deserialize;

pub type BootloaderVersion = u64;

pub(crate) type ProgramIdentifiers = HashMap<String, Identifier>;

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct BootloaderConfig {
    pub simple_bootloader_program_hash: Felt252,
    pub supported_cairo_verifier_program_hashes: Vec<Felt252>,
}

#[derive(Deserialize, Debug, Default, Clone, PartialEq)]
pub struct CompositePackedOutput {
    pub outputs: Vec<Felt252>,
    pub subtasks: Vec<PackedOutput>,
}

impl CompositePackedOutput {
    pub fn elements_for_hash(&self) -> &Vec<Felt252> {
        &self.outputs
    }
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub enum PackedOutput {
    Plain(Vec<Felt252>),
    Composite(CompositePackedOutput),
}

#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::large_enum_variant)]
pub enum Task {
    Program(Program),
    Pie(CairoPie),
}

impl Task {
    pub fn get_program(&self) -> Result<StrippedProgram, ProgramError> {
        // TODO: consider whether declaring a struct similar to StrippedProgram
        //       but that uses a reference to data to avoid copying is worth the effort.
        match self {
            Task::Program(program) => program.get_stripped_program(),
            Task::Pie(cairo_pie) => Ok(cairo_pie.metadata.program.clone()),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TaskSpec {
    pub task: Task,
}

impl TaskSpec {
    pub fn load_task(&self) -> &Task {
        &self.task
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SimpleBootloaderInput {
    pub fact_topologies_path: Option<PathBuf>,
    pub single_page: bool,
    pub tasks: Vec<TaskSpec>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BootloaderInput {
    pub simple_bootloader_input: SimpleBootloaderInput,
    pub bootloader_config: BootloaderConfig,
    pub packed_outputs: Vec<PackedOutput>,
}

impl BootloaderInput {
    pub fn from_tasks(tasks: Vec<TaskSpec>) -> Self {
        let n_tasks = tasks.len();
        Self {
            simple_bootloader_input: SimpleBootloaderInput {
                fact_topologies_path: None,
                single_page: false,
                tasks,
            },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: Felt252::from(0),
                supported_cairo_verifier_program_hashes: vec![],
            },
            packed_outputs: vec![PackedOutput::Plain(vec![]); n_tasks],
        }
    }
}
