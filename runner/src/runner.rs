use std::fs::File;
use std::path::Path;
use std::path::PathBuf;

use bincode::error::EncodeError;
use cairo_vm::air_private_input::AirPrivateInput;
use cairo_vm::air_public_input::{PublicInput, PublicInputError};
use cairo_vm::cairo_run::{
    cairo_run_program_with_initial_scope, write_encoded_memory, write_encoded_trace,
    CairoRunConfig, EncodeTraceError,
};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::trace_errors::TraceError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;
use cairo_vm::Felt252;
use bootloader::{
    insert_bootloader_input, BootloaderConfig, BootloaderHintProcessor, BootloaderInput,
    PackedOutput, SimpleBootloaderInput, TaskSpec,
};
use serde::Serialize;
use thiserror::Error;

pub fn cairo_run_bootloader_in_proof_mode(
    bootloader_program: &Program,
    tasks: Vec<TaskSpec>,
    layout: LayoutName,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = BootloaderHintProcessor::new();

    let cairo_run_config = CairoRunConfig {
        entrypoint: "main",
        trace_enabled: true,
        relocate_mem: true,
        layout: layout,
        proof_mode: true,
        secure_run: None,
        disable_trace_padding: false,
        allow_missing_builtins: None,
        dynamic_layout_params: None,
    };

    // Build the bootloader input
    let n_tasks = tasks.len();

    let bootloader_input = BootloaderInput {
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
    };

    // Note: the method used to set the bootloader input depends on
    // https://github.com/lambdaclass/cairo-vm/pull/1772 and may change depending on review.
    let mut exec_scopes = ExecutionScopes::new();
    insert_bootloader_input(&mut exec_scopes, bootloader_input);

    // Run the bootloader
    cairo_run_program_with_initial_scope(
        &bootloader_program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )
}

pub struct ExecutionArtifacts<'a> {
    pub public_input: PublicInput<'a>,
    pub private_input: AirPrivateInput,
    pub memory: Vec<u8>,
    pub trace: Vec<u8>,
}

#[derive(Error, Debug)]
pub enum ExecutionError {
    #[error(transparent)]
    RunFailed(#[from] CairoRunError),
    #[error(transparent)]
    GeneratePublicInput(#[from] PublicInputError),
    #[error(transparent)]
    GenerateTrace(#[from] TraceError),
    #[error(transparent)]
    EncodeMemory(EncodeTraceError),
    #[error(transparent)]
    EncodeTrace(EncodeTraceError),
    #[error(transparent)]
    SerializePublicInput(#[from] serde_json::Error),
}

/// An in-memory writer for bincode encoding.
#[derive(Default)]
pub struct MemWriter {
    pub buf: Vec<u8>,
}

impl MemWriter {
    pub fn new() -> Self {
        Self::default()
    }
}

impl bincode::enc::write::Writer for MemWriter {
    fn write(&mut self, bytes: &[u8]) -> Result<(), EncodeError> {
        self.buf.extend_from_slice(bytes);
        Ok(())
    }
}

/// Extracts execution artifacts from the runner and VM (after execution).
///
/// * `cairo_runner` Cairo runner object.
/// * `vm`: Cairo VM object.
pub fn extract_execution_artifacts(cairo_runner: CairoRunner) -> Result<(), ExecutionError> {
    let memory = &cairo_runner.relocated_memory;
    let trace = cairo_runner
        .relocated_trace
        .as_ref()
        .ok_or(ExecutionError::GenerateTrace(TraceError::TraceNotEnabled))?;

    let mut memory_writer = MemWriter::new();
    write_encoded_memory(memory, &mut memory_writer).map_err(ExecutionError::EncodeMemory)?;
    let memory_raw = memory_writer.buf;

    let mut trace_writer = MemWriter::new();
    write_encoded_trace(trace, &mut trace_writer).map_err(ExecutionError::EncodeTrace)?;
    let trace_raw = trace_writer.buf;

    let cairo_vm_public_input = cairo_runner.get_air_public_input()?;
    let public_input = PublicInput::try_from(cairo_vm_public_input).unwrap();

    let private_input = cairo_runner.get_air_private_input().to_owned();

    let tmp_dir_path = PathBuf::from("proof");

    let public_input_file = tmp_dir_path.join("public_input.json");
    let private_input_file = tmp_dir_path.join("private_input.json");
    let memory_file = tmp_dir_path.join("memory.bin");
    let trace_file = tmp_dir_path.join("trace.bin");
    write_json_to_file(public_input, &public_input_file).unwrap();
    let private_input_serializable = private_input.to_serializable(
        trace_file.to_string_lossy().to_string(),
        memory_file.to_string_lossy().to_string(),
    );
    write_json_to_file(private_input_serializable, &private_input_file).unwrap();

    std::fs::write(&memory_file, memory_raw).unwrap();
    std::fs::write(&trace_file, trace_raw).unwrap();
    Ok(())
}

pub fn write_json_to_file<T: Serialize, P: AsRef<Path>>(
    obj: T,
    path: P,
) -> Result<(), std::io::Error> {
    let mut file = File::create(path)?;
    serde_json::to_writer(&mut file, &obj)?;
    Ok(())
}
