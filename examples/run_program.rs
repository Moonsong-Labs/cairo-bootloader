use std::error::Error;

use cairo_vm::cairo_run::{cairo_run_program, CairoRunConfig};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;
use cairo_vm::Felt252;

use cairo_bootloader::bootloaders::load_bootloader;
use cairo_bootloader::tasks::make_bootloader_tasks;
use cairo_bootloader::{
    insert_bootloader_input, BootloaderConfig, BootloaderHintProcessor, BootloaderInput,
    PackedOutput, SimpleBootloaderInput, TaskSpec,
};

fn cairo_run_bootloader_in_proof_mode(
    bootloader_program: &Program,
    tasks: Vec<TaskSpec>,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = BootloaderHintProcessor::new();

    let cairo_run_config = CairoRunConfig {
        entrypoint: "main",
        trace_enabled: false,
        relocate_mem: false,
        layout: LayoutName::starknet_with_keccak,
        proof_mode: true,
        secure_run: None,
        disable_trace_padding: false,
        allow_missing_builtins: None,
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
    cairo_run_program(
        &bootloader_program,
        &cairo_run_config,
        &mut hint_processor,
        Some(exec_scopes),
    )
}

fn main() -> Result<(), Box<dyn Error>> {
    let bootloader_program = load_bootloader()?;
    let fibonacci_program = include_bytes!("fibonacci.json");

    let tasks = make_bootloader_tasks(&[fibonacci_program], &[])?;

    let mut runner = cairo_run_bootloader_in_proof_mode(&bootloader_program, tasks)?;

    let mut output_buffer = "Program Output:\n".to_string();
    runner.vm.write_output(&mut output_buffer)?;
    print!("{output_buffer}");

    Ok(())
}
