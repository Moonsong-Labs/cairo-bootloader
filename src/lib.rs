pub mod hints;
pub mod tasks;

use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::program::Program;
pub use hints::*;

const BOOTLOADER_V0_13_1: &[u8] = include_bytes!("../resources/bootloader-0.13.1.json");

/// Loads the bootloader and returns it as a Cairo VM `Program` object.
pub fn load_bootloader() -> Result<Program, ProgramError> {
    Program::from_bytes(BOOTLOADER_V0_13_1, Some("main"))
}

/// Inserts the bootloader input in the execution scopes.
pub fn insert_bootloader_input(
    exec_scopes: &mut ExecutionScopes,
    bootloader_input: BootloaderInput,
) {
    exec_scopes.insert_value(BOOTLOADER_INPUT, bootloader_input);
}
