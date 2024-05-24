/// Deserialized bootloader input.
pub const BOOTLOADER_INPUT: &str = "bootloader_input";

/// The bootloader program, as a Program object.
pub const BOOTLOADER_PROGRAM_IDENTIFIERS: &str = "bootloader_program";

/// Saved state of the output builtin.
pub const OUTPUT_BUILTIN_STATE: &str = "output_builtin_state";

/// Output builtin segment start.
pub const OUTPUT_START: &str = "output_start";

/// Deserialized simple bootloader input.
pub const SIMPLE_BOOTLOADER_INPUT: &str = "simple_bootloader_input";

/// Packed outputs.
pub const PACKED_OUTPUTS: &str = "packed_outputs";

/// Packed output for the current task.
pub const PACKED_OUTPUT: &str = "packed_output";

/// Fact topologies.
pub const FACT_TOPOLOGIES: &str = "fact_topologies";

/// Simple bootloader tasks.
pub const TASKS: &str = "tasks";

/// Current simple bootloader task.
pub const TASK: &str = "task";

/// Program data segment. Used in `execute_task()`.
pub const PROGRAM_DATA_BASE: &str = "program_data_base";

/// Address of current program.
pub const PROGRAM_ADDRESS: &str = "program_address";

/// Output builtin additional data.
pub const OUTPUT_RUNNER_DATA: &str = "output_runner_data";

/// Number of builtins used by the program.
pub const N_BUILTINS: &str = "n_builtins";

/// Number of selected builtins for the current program.
pub const N_SELECTED_BUILTINS: &str = "n_selected_builtins";

/// "pre_execution_builtin_ptrs"
pub const PRE_EXECUTION_BUILTIN_PTRS: &str = "pre_execution_builtin_ptrs";
