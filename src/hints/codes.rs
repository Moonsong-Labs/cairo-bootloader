pub const BOOTLOADER_PREPARE_SIMPLE_BOOTLOADER_OUTPUT_SEGMENT: &str =
    "from starkware.cairo.bootloaders.bootloader.objects import BootloaderInput
bootloader_input = BootloaderInput.Schema().load(program_input)

ids.simple_bootloader_output_start = segments.add()

# Change output builtin state to a different segment in preparation for calling the
# simple bootloader.
output_builtin_state = output_builtin.get_state()
output_builtin.new_state(base=ids.simple_bootloader_output_start)";

pub const BOOTLOADER_PREPARE_SIMPLE_BOOTLOADER_INPUT: &str =
    "simple_bootloader_input = bootloader_input";

pub const BOOTLOADER_RESTORE_BOOTLOADER_OUTPUT: &str =
    "# Restore the bootloader's output builtin state.
output_builtin.set_state(output_builtin_state)";

pub const BOOTLOADER_LOAD_BOOTLOADER_CONFIG: &str =
    "from starkware.cairo.bootloaders.bootloader.objects import BootloaderConfig
bootloader_config: BootloaderConfig = bootloader_input.bootloader_config

ids.bootloader_config = segments.gen_arg(
    [
        bootloader_config.simple_bootloader_program_hash,
        len(bootloader_config.supported_cairo_verifier_program_hashes),
        bootloader_config.supported_cairo_verifier_program_hashes,
    ],
)";

pub const BOOTLOADER_ENTER_PACKED_OUTPUT_SCOPE: &str =
    "from starkware.cairo.bootloaders.bootloader.objects import PackedOutput

task_id = len(packed_outputs) - ids.n_subtasks
packed_output: PackedOutput = packed_outputs[task_id]

vm_enter_scope(new_scope_locals=dict(packed_output=packed_output))";

pub const BOOTLOADER_IMPORT_PACKED_OUTPUT_SCHEMAS: &str =
    "from starkware.cairo.bootloaders.bootloader.objects import (
    CompositePackedOutput,
    PlainPackedOutput,
)";

// Appears as nondet %{ isinstance(packed_output, PlainPackedOutput) %} in the code.
pub const BOOTLOADER_IS_PLAIN_PACKED_OUTPUT: &str =
    "memory[ap] = to_felt_or_relocatable(isinstance(packed_output, PlainPackedOutput))";

pub const BOOTLOADER_SAVE_OUTPUT_POINTER: &str = "output_start = ids.output_ptr";

pub const BOOTLOADER_SAVE_PACKED_OUTPUTS: &str = "packed_outputs = bootloader_input.packed_outputs";

pub const BOOTLOADER_COMPUTE_FACT_TOPOLOGIES: &str = "from typing import List

from starkware.cairo.bootloaders.bootloader.utils import compute_fact_topologies
from starkware.cairo.bootloaders.fact_topology import FactTopology
from starkware.cairo.bootloaders.simple_bootloader.utils import (
    configure_fact_topologies,
    write_to_fact_topologies_file,
)

# Compute the fact topologies of the plain packed outputs based on packed_outputs and
# fact_topologies of the inner tasks.
plain_fact_topologies: List[FactTopology] = compute_fact_topologies(
    packed_outputs=packed_outputs, fact_topologies=fact_topologies,
)

# Configure the memory pages in the output builtin, based on plain_fact_topologies.
configure_fact_topologies(
    fact_topologies=plain_fact_topologies, output_start=output_start,
    output_builtin=output_builtin,
)

# Dump fact topologies to a json file.
if bootloader_input.fact_topologies_path is not None:
    write_to_fact_topologies_file(
        fact_topologies_path=bootloader_input.fact_topologies_path,
        fact_topologies=plain_fact_topologies,
    )";

pub const BOOTLOADER_GUESS_PRE_IMAGE_OF_SUBTASKS_OUTPUT_HASH: &str =
    "data = packed_output.elements_for_hash()
ids.nested_subtasks_output_len = len(data)
ids.nested_subtasks_output = segments.gen_arg(data)";

pub const BOOTLOADER_SET_PACKED_OUTPUT_TO_SUBTASKS: &str =
    "packed_outputs = packed_output.subtasks";

pub const BOOTLOADER_ASSERT_IS_COMPOSITE_PACKED_OUTPUT: &str =
    "assert isinstance(packed_output, CompositePackedOutput)";

pub const SIMPLE_BOOTLOADER_PREPARE_TASK_RANGE_CHECKS: &str =
    "n_tasks = len(simple_bootloader_input.tasks)
memory[ids.output_ptr] = n_tasks

# Task range checks are located right after simple bootloader validation range checks, and
# this is validated later in this function.
ids.task_range_check_ptr = ids.range_check_ptr + ids.BuiltinData.SIZE * n_tasks

# A list of fact_toplogies that instruct how to generate the fact from the program output
# for each task.
fact_topologies = []";

pub const SIMPLE_BOOTLOADER_SET_TASKS_VARIABLE: &str = "tasks = simple_bootloader_input.tasks";

// Appears as nondet %{ ids.num // 2 %} in the code.
pub const SIMPLE_BOOTLOADER_DIVIDE_NUM_BY_2: &str =
    "memory[ap] = to_felt_or_relocatable(ids.num // 2)";

pub const SIMPLE_BOOTLOADER_SET_CURRENT_TASK: &str =
    "from starkware.cairo.bootloaders.simple_bootloader.objects import Task

# Pass current task to execute_task.
task_id = len(simple_bootloader_input.tasks) - ids.n_tasks
task = simple_bootloader_input.tasks[task_id].load_task()";

// Appears as nondet %{ 0 %} in the code.
pub const SIMPLE_BOOTLOADER_ZERO: &str = "memory[ap] = to_felt_or_relocatable(0)";

pub const EXECUTE_TASK_ALLOCATE_PROGRAM_DATA_SEGMENT: &str =
    "ids.program_data_ptr = program_data_base = segments.add()";

pub const EXECUTE_TASK_LOAD_PROGRAM: &str =
    "from starkware.cairo.bootloaders.simple_bootloader.utils import load_program

# Call load_program to load the program header and code to memory.
program_address, program_data_size = load_program(
    task=task, memory=memory, program_header=ids.program_header,
    builtins_offset=ids.ProgramHeader.builtin_list)
segments.finalize(program_data_base.segment_index, program_data_size)";

pub const EXECUTE_TASK_VALIDATE_HASH: &str = "# Validate hash.
from starkware.cairo.bootloaders.hash_program import compute_program_hash_chain

assert memory[ids.output_ptr + 1] == compute_program_hash_chain(task.get_program()), \\
  'Computed hash does not match input.'";

pub const EXECUTE_TASK_ASSERT_PROGRAM_ADDRESS: &str = "# Sanity check.
assert ids.program_address == program_address";

pub const EXECUTE_TASK_CALL_TASK: &str =
    "from starkware.cairo.bootloaders.simple_bootloader.objects import (
    CairoPieTask,
    RunProgramTask,
    Task,
)
from starkware.cairo.bootloaders.simple_bootloader.utils import (
    load_cairo_pie,
    prepare_output_runner,
)

assert isinstance(task, Task)
n_builtins = len(task.get_program().builtins)
new_task_locals = {}
if isinstance(task, RunProgramTask):
    new_task_locals['program_input'] = task.program_input
    new_task_locals['WITH_BOOTLOADER'] = True

    vm_load_program(task.program, program_address)
elif isinstance(task, CairoPieTask):
    ret_pc = ids.ret_pc_label.instruction_offset_ - ids.call_task.instruction_offset_ + pc
    load_cairo_pie(
        task=task.cairo_pie, memory=memory, segments=segments,
        program_address=program_address, execution_segment_address= ap - n_builtins,
        builtin_runners=builtin_runners, ret_fp=fp, ret_pc=ret_pc)
else:
    raise NotImplementedError(f'Unexpected task type: {type(task).__name__}.')

output_runner_data = prepare_output_runner(
    task=task,
    output_builtin=output_builtin,
    output_ptr=ids.pre_execution_builtin_ptrs.output)
vm_enter_scope(new_task_locals)";

pub const EXECUTE_TASK_EXIT_SCOPE: &str = "vm_exit_scope()
# Note that bootloader_input will only be available in the next hint.";

pub const EXECUTE_TASK_WRITE_RETURN_BUILTINS: &str =
    "from starkware.cairo.bootloaders.simple_bootloader.utils import write_return_builtins

# Fill the values of all builtin pointers after executing the task.
builtins = task.get_program().builtins
write_return_builtins(
    memory=memory, return_builtins_addr=ids.return_builtin_ptrs.address_,
    used_builtins=builtins, used_builtins_addr=ids.used_builtins_addr,
    pre_execution_builtins_addr=ids.pre_execution_builtin_ptrs.address_, task=task)

vm_enter_scope({'n_selected_builtins': n_builtins})";

pub const EXECUTE_TASK_APPEND_FACT_TOPOLOGIES: &str =
    "from starkware.cairo.bootloaders.simple_bootloader.utils import get_task_fact_topology

# Add the fact topology of the current task to 'fact_topologies'.
output_start = ids.pre_execution_builtin_ptrs.output
output_end = ids.return_builtin_ptrs.output
fact_topologies.append(get_task_fact_topology(
    output_size=output_end - output_start,
    task=task,
    output_builtin=output_builtin,
    output_runner_data=output_runner_data,
))";

pub const SELECT_BUILTINS_ENTER_SCOPE: &str =
    "vm_enter_scope({'n_selected_builtins': ids.n_selected_builtins})";

pub const INNER_SELECT_BUILTINS_SELECT_BUILTIN: &str =
    "# A builtin should be selected iff its encoding appears in the selected encodings list
# and the list wasn't exhausted.
# Note that testing inclusion by a single comparison is possible since the lists are sorted.
ids.select_builtin = int(
  n_selected_builtins > 0 and memory[ids.selected_encodings] == memory[ids.all_encodings])
if ids.select_builtin:
  n_selected_builtins = n_selected_builtins - 1";
