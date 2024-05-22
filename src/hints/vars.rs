/// Deserialized bootloader input.
pub(crate) const BOOTLOADER_INPUT: &str = "bootloader_input";

/// The bootloader program, as a Program object.
pub(crate) const BOOTLOADER_PROGRAM_IDENTIFIERS: &str = "bootloader_program";

/// Saved state of the output builtin.
pub(crate) const OUTPUT_BUILTIN_STATE: &str = "output_builtin_state";

/// Output builtin segment start.
pub(crate) const OUTPUT_START: &str = "output_start";

/// Deserialized simple bootloader input.
pub(crate) const SIMPLE_BOOTLOADER_INPUT: &str = "simple_bootloader_input";

/// Packed outputs.
pub(crate) const PACKED_OUTPUTS: &str = "packed_outputs";

/// Packed output for the current task.
pub(crate) const PACKED_OUTPUT: &str = "packed_output";

/// Fact topologies.
pub(crate) const FACT_TOPOLOGIES: &str = "fact_topologies";

/// Simple bootloader tasks.
pub(crate) const TASKS: &str = "tasks";

/// Current simple bootloader task.
pub(crate) const TASK: &str = "task";

/// Program data segment. Used in `execute_task()`.
pub(crate) const PROGRAM_DATA_BASE: &str = "program_data_base";

/// Address of current program.
pub(crate) const PROGRAM_ADDRESS: &str = "program_address";

/// Output builtin additional data.
pub(crate) const OUTPUT_RUNNER_DATA: &str = "output_runner_data";

/// Number of builtins used by the program.
pub(crate) const N_BUILTINS: &str = "n_builtins";

/// Number of selected builtins for the current program.
pub(crate) const N_SELECTED_BUILTINS: &str = "n_selected_builtins";

/// "pre_execution_builtin_ptrs"
pub(crate) const PRE_EXECUTION_BUILTIN_PTRS: &str = "pre_execution_builtin_ptrs";
