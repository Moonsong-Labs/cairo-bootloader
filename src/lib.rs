use cairo_vm::types::exec_scope::ExecutionScopes;
pub use hints::*;

pub mod bootloaders;
mod hints;
pub mod tasks;

#[cfg(test)]
pub mod macros;

/// Inserts the bootloader input in the execution scopes.
pub fn insert_bootloader_input(
    exec_scopes: &mut ExecutionScopes,
    bootloader_input: BootloaderInput,
) {
    exec_scopes.insert_value(BOOTLOADER_INPUT, bootloader_input);
}