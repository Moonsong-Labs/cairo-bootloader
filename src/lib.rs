use crate::hints::types::ProgramIdentifiers;
use cairo_vm::cairo_run::{cairo_run_program_with_initial_scope, CairoRunConfig};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;
pub use hints::*;

pub mod bootloaders;
mod hints;
pub mod tasks;

#[cfg(test)]
pub mod macros;

/// Inserts the bootloader input and program identifiers in the execution scopes.
pub fn prepare_bootloader_exec_scopes(
    exec_scopes: &mut ExecutionScopes,
    bootloader_input: BootloaderInput,
    bootloader_program: &Program,
) {
    exec_scopes.insert_value(BOOTLOADER_INPUT, bootloader_input);
    let identifiers: ProgramIdentifiers = bootloader_program
        .iter_identifiers()
        .map(|(k, v)| (k.to_string(), v.clone()))
        .collect();
    exec_scopes.insert_value(BOOTLOADER_PROGRAM_IDENTIFIERS, identifiers);
}

/// A helper function to run the bootloader in proof mode.
///
/// Reimplement your own version of this function if you wish to modify the Cairo run config
/// or other parameters.
pub fn cairo_run_bootloader_in_proof_mode(
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
    let bootloader_input = BootloaderInput::from_tasks(tasks);

    // Load initial variables in the exec scopes
    let mut exec_scopes = ExecutionScopes::new();
    prepare_bootloader_exec_scopes(&mut exec_scopes, bootloader_input, bootloader_program);

    // Run the bootloader
    cairo_run_program_with_initial_scope(
        bootloader_program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )
}
