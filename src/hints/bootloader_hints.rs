use crate::hints::fact_topologies::{
    compute_fact_topologies, configure_fact_topologies, write_to_fact_topologies_file, FactTopology,
};
use cairo_vm::any_box;
use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::{
    get_integer_from_var_name, get_ptr_from_var_name, insert_value_from_var_name,
    insert_value_into_ap,
};
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::errors::memory_errors::MemoryError;
use cairo_vm::vm::runners::builtin_runner::OutputBuiltinState;
use cairo_vm::vm::vm_core::VirtualMachine;
use num_traits::ToPrimitive;
use std::any::Any;
use std::collections::HashMap;

use crate::hints::types::{BootloaderInput, CompositePackedOutput, PackedOutput};
use crate::hints::vars;

/// Implements
/// ```no-run
/// %{
///     from starkware.cairo.bootloaders.bootloader.objects import BootloaderInput
///     bootloader_input = BootloaderInput.Schema().load(program_input)
///
///     ids.simple_bootloader_output_start = segments.add()
///
///     # Change output builtin state to a different segment in preparation for calling the
///     # simple bootloader.
///     output_builtin_state = output_builtin.get_state()
///     output_builtin.new_state(base=ids.simple_bootloader_output_start)
/// %}
/// ```
pub fn prepare_simple_bootloader_output_segment(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // Python: bootloader_input = BootloaderInput.Schema().load(program_input)
    // -> Assert that the bootloader input has been loaded when setting up the VM
    let _bootloader_input: &BootloaderInput = exec_scopes.get_ref(vars::BOOTLOADER_INPUT)?;

    // Python: ids.simple_bootloader_output_start = segments.add()
    let new_segment_base = vm.add_memory_segment();
    insert_value_from_var_name(
        "simple_bootloader_output_start",
        new_segment_base,
        vm,
        ids_data,
        ap_tracking,
    )?;

    // Python:
    // output_builtin_state = output_builtin.get_state()
    // output_builtin.new_state(base=ids.simple_bootloader_output_start)
    let output_builtin = vm.get_output_builtin_mut()?;
    let output_builtin_state = output_builtin.get_state();
    output_builtin.new_state(new_segment_base.segment_index as usize, true);
    exec_scopes.insert_value(vars::OUTPUT_BUILTIN_STATE, output_builtin_state);

    insert_value_from_var_name(
        "simple_bootloader_output_start",
        new_segment_base,
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

/// Implements %{ simple_bootloader_input = bootloader_input %}
pub fn prepare_simple_bootloader_input(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
    let bootloader_input: BootloaderInput = exec_scopes.get(vars::BOOTLOADER_INPUT)?;
    exec_scopes.insert_value(
        vars::SIMPLE_BOOTLOADER_INPUT,
        bootloader_input.simple_bootloader_input,
    );

    Ok(())
}

/// Implements
/// # Restore the bootloader's output builtin state.
/// output_builtin.set_state(output_builtin_state)
pub fn restore_bootloader_output(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let output_builtin_state: OutputBuiltinState = exec_scopes.get(vars::OUTPUT_BUILTIN_STATE)?;
    vm.get_output_builtin_mut()?.set_state(output_builtin_state);

    Ok(())
}
/// Mimics the behaviour of the Python VM `gen_arg`.
///
/// Creates a new segment for each vector encountered in `args`. For each new
/// segment, the pointer to the segment will be added to the current segment.
///
/// Example: `vec![1, 2, vec![3, 4]]`
/// -> Allocates segment N, starts writing at offset 0:
/// (N, 0): 1       # Write the values of the vector one by one
/// (N, 1): 2
/// -> a vector is encountered, allocate a new segment
/// (N, 2): N+1     # Pointer to the new segment
/// (N+1, 0): 3     # Write the values of the nested vector
/// (N+1, 1): 4
fn gen_arg(vm: &mut VirtualMachine, args: &Vec<Box<dyn Any>>) -> Result<Relocatable, MemoryError> {
    let base = vm.segments.add();
    let mut ptr = base;

    for arg in args {
        if let Some(value) = arg.downcast_ref::<MaybeRelocatable>() {
            ptr = vm.segments.load_data(ptr, &vec![value.clone()])?;
        } else if let Some(vector) = arg.downcast_ref::<Vec<Box<dyn Any>>>() {
            let nested_base = gen_arg(vm, vector)?;
            ptr = vm.segments.load_data(ptr, &vec![nested_base.into()])?;
        } else {
            return Err(MemoryError::GenArgInvalidType);
        }
    }

    Ok(base)
}

/// Implements
/// from starkware.cairo.bootloaders.bootloader.objects import BootloaderConfig
/// bootloader_config: BootloaderConfig = bootloader_input.bootloader_config
///
/// ids.bootloader_config = segments.gen_arg(
///     [
///         bootloader_config.simple_bootloader_program_hash,
///         len(bootloader_config.supported_cairo_verifier_program_hashes),
///         bootloader_config.supported_cairo_verifier_program_hashes,
///     ],
/// )
pub fn load_bootloader_config(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let bootloader_input: BootloaderInput = exec_scopes.get(vars::BOOTLOADER_INPUT)?;
    let config = bootloader_input.bootloader_config;

    // Organize args as
    // [
    //     bootloader_config.simple_bootloader_program_hash,
    //     len(bootloader_config.supported_cairo_verifier_program_hashes),
    //     bootloader_config.supported_cairo_verifier_program_hashes,
    // ]
    let mut program_hashes = Vec::<Box<dyn Any>>::new();
    for program_hash in &config.supported_cairo_verifier_program_hashes {
        program_hashes.push(Box::new(MaybeRelocatable::from(program_hash)));
    }

    let args: Vec<Box<dyn Any>> = vec![
        any_box!(MaybeRelocatable::from(
            config.simple_bootloader_program_hash
        )),
        any_box!(MaybeRelocatable::from(
            config.supported_cairo_verifier_program_hashes.len()
        )),
        any_box!(program_hashes),
    ];

    // Store the args in the VM memory
    let args_segment = gen_arg(vm, &args)?;
    insert_value_from_var_name("bootloader_config", args_segment, vm, ids_data, ap_tracking)?;

    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.bootloader.objects import PackedOutput
///
/// task_id = len(packed_outputs) - ids.n_subtasks
/// packed_output: PackedOutput = packed_outputs[task_id]
///
/// vm_enter_scope(new_scope_locals=dict(packed_output=packed_output))
pub fn enter_packed_output_scope(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // task_id = len(packed_outputs) - ids.n_subtasks
    let packed_outputs: Vec<PackedOutput> = exec_scopes.get(vars::PACKED_OUTPUTS)?;
    let n_subtasks = get_integer_from_var_name("n_subtasks", vm, ids_data, ap_tracking)
        .unwrap()
        .to_usize()
        .unwrap();
    let task_id = packed_outputs.len() - n_subtasks;
    // packed_output: PackedOutput = packed_outputs[task_id]
    let packed_output: Box<dyn Any> = Box::new(packed_outputs[task_id].clone());

    // vm_enter_scope(new_scope_locals=dict(packed_output=packed_output))
    exec_scopes.enter_scope(HashMap::from([(
        vars::PACKED_OUTPUT.to_string(),
        packed_output,
    )]));

    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.bootloader.objects import (
///     CompositePackedOutput,
///     PlainPackedOutput,
/// )
pub fn import_packed_output_schemas() -> Result<(), HintError> {
    // Nothing to do!
    Ok(())
}

/// Implements %{ isinstance(packed_output, PlainPackedOutput) %}
/// (compiled to %{ memory[ap] = to_felt_or_relocatable(isinstance(packed_output, PlainPackedOutput)) %}).
///
/// Stores the result in the `ap` register to be accessed by the program.
pub fn is_plain_packed_output(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let packed_output: PackedOutput = exec_scopes.get(vars::PACKED_OUTPUT)?;
    let result = match packed_output {
        PackedOutput::Plain(_) => 1,
        _ => 0,
    };
    insert_value_into_ap(vm, result)?;

    Ok(())
}

/// Implements
/// %{ assert isinstance(packed_output, CompositePackedOutput) %}
pub fn assert_is_composite_packed_output(
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let packed_output: PackedOutput = exec_scopes.get(vars::PACKED_OUTPUT)?;

    match packed_output {
        PackedOutput::Composite(_) => Ok(()),
        other => Err(HintError::CustomHint(
            format!("Expected composite packed output, got {:?}", other).into_boxed_str(),
        )),
    }
}

/*
Implements hint:
%{
    output_start = ids.output_ptr
%}
*/
pub fn save_output_pointer(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    exec_scopes.insert_value(vars::OUTPUT_START, output_ptr);
    Ok(())
}

/*
Implements hint:
%{
    packed_outputs = bootloader_input.packed_outputs
%}
*/
pub fn save_packed_outputs(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
    let bootloader_input: &BootloaderInput = exec_scopes.get_ref("bootloader_input")?;
    let packed_outputs = bootloader_input.packed_outputs.clone();
    exec_scopes.insert_value("packed_outputs", packed_outputs);
    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.bootloader.utils import compute_fact_topologies
/// from starkware.cairo.bootloaders.fact_topology import FactTopology
/// from starkware.cairo.bootloaders.simple_bootloader.utils import (
///     configure_fact_topologies,
///     write_to_fact_topologies_file,
/// )
///
/// # Compute the fact topologies of the plain packed outputs based on packed_outputs and
/// # fact_topologies of the inner tasks.
/// plain_fact_topologies: List[FactTopology] = compute_fact_topologies(
///     packed_outputs=packed_outputs, fact_topologies=fact_topologies,
/// )
///
/// # Configure the memory pages in the output builtin, based on plain_fact_topologies.
/// configure_fact_topologies(
///     fact_topologies=plain_fact_topologies, output_start=output_start,
///     output_builtin=output_builtin,
/// )
///
/// # Dump fact topologies to a json file.
/// if bootloader_input.fact_topologies_path is not None:
///     write_to_fact_topologies_file(
///         fact_topologies_path=bootloader_input.fact_topologies_path,
///         fact_topologies=plain_fact_topologies,
///     )
pub fn compute_and_configure_fact_topologies(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let packed_outputs: Vec<PackedOutput> = exec_scopes.get(vars::PACKED_OUTPUTS)?;
    let fact_topologies: Vec<FactTopology> = exec_scopes.get(vars::FACT_TOPOLOGIES)?;
    let mut output_start: Relocatable = exec_scopes.get(vars::OUTPUT_START)?;
    let output_builtin = vm.get_output_builtin_mut()?;

    let plain_fact_topologies = compute_fact_topologies(&packed_outputs, &fact_topologies)
        .map_err(Into::<HintError>::into)?;

    configure_fact_topologies(&plain_fact_topologies, &mut output_start, output_builtin)
        .map_err(Into::<HintError>::into)?;

    exec_scopes.insert_value(vars::OUTPUT_START, output_start);

    let bootloader_input: &BootloaderInput = exec_scopes.get_ref(vars::BOOTLOADER_INPUT)?;
    if let Some(path) = &bootloader_input
        .simple_bootloader_input
        .fact_topologies_path
    {
        write_to_fact_topologies_file(path.as_path(), &plain_fact_topologies)
            .map_err(Into::<HintError>::into)?;
    }

    Ok(())
}

fn unwrap_composite_output(
    packed_output: PackedOutput,
) -> Result<CompositePackedOutput, HintError> {
    match packed_output {
        PackedOutput::Plain(_) => Err(HintError::CustomHint(
            "Expected packed output to be composite"
                .to_string()
                .into_boxed_str(),
        )),
        PackedOutput::Composite(composite_packed_output) => Ok(composite_packed_output),
    }
}

/*
Implements hint:
%{
    packed_outputs = packed_output.subtasks
%}
*/
pub fn set_packed_output_to_subtasks(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
    let packed_output: PackedOutput = exec_scopes.get(vars::PACKED_OUTPUT)?;
    let composite_packed_output = unwrap_composite_output(packed_output)?;
    let subtasks = composite_packed_output.subtasks;
    exec_scopes.insert_value(vars::PACKED_OUTPUTS, subtasks);

    Ok(())
}

/*
Implements hint:
%{
    data = packed_output.elements_for_hash()
    ids.nested_subtasks_output_len = len(data)
    ids.nested_subtasks_output = segments.gen_arg(data)";
%}
*/
pub fn guess_pre_image_of_subtasks_output_hash(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let packed_output: PackedOutput = exec_scopes.get(vars::PACKED_OUTPUT)?;
    let composite_packed_output = unwrap_composite_output(packed_output)?;

    let data = composite_packed_output.elements_for_hash();
    insert_value_from_var_name(
        "nested_subtasks_output_len",
        data.len(),
        vm,
        ids_data,
        ap_tracking,
    )?;
    let args = data
        .iter()
        .cloned()
        .map(|x| Box::new(MaybeRelocatable::Int(x)) as Box<dyn Any>)
        .collect();
    let nested_subtasks_output = gen_arg(vm, &args)?;
    insert_value_from_var_name(
        "nested_subtasks_output",
        nested_subtasks_output,
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

/*
Implements hint:
%{
    # Sanity check.
    assert ids.program_address == program_address"
%}
*/
pub fn assert_program_address(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let ids_program_address =
        get_ptr_from_var_name(vars::PROGRAM_ADDRESS, vm, ids_data, ap_tracking)?;
    let program_address: Relocatable = exec_scopes.get(vars::PROGRAM_ADDRESS)?;

    if ids_program_address != program_address {
        return Err(HintError::CustomHint(
            "program address is incorrect".to_string().into_boxed_str(),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use num_traits::ToPrimitive;

    use crate::hints::codes::{
        BOOTLOADER_GUESS_PRE_IMAGE_OF_SUBTASKS_OUTPUT_HASH, BOOTLOADER_SAVE_OUTPUT_POINTER,
        BOOTLOADER_SAVE_PACKED_OUTPUTS, BOOTLOADER_SET_PACKED_OUTPUT_TO_SUBTASKS,
        EXECUTE_TASK_ASSERT_PROGRAM_ADDRESS,
    };
    use crate::hints::types::{BootloaderConfig, SimpleBootloaderInput};
    use crate::{
        add_segments, define_segments, ids_data, run_hint, vm, MinimalBootloaderHintProcessor,
    };
    use assert_matches::assert_matches;
    use cairo_vm::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::HintProcessorData;
    use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::get_maybe_relocatable_from_var_name;
    use cairo_vm::hint_processor::hint_processor_definition::HintProcessorLogic;
    use cairo_vm::serde::deserialize_program::OffsetValue;
    use cairo_vm::vm::runners::builtin_runner::{
        BuiltinRunner, OutputBuiltinRunner, OutputBuiltinState,
    };
    use cairo_vm::vm::runners::cairo_pie::PublicMemoryPage;
    use cairo_vm::{any_box, relocatable, Felt252};
    use rstest::{fixture, rstest};

    use super::*;

    #[fixture]
    fn bootloader_input() -> BootloaderInput {
        BootloaderInput {
            simple_bootloader_input: SimpleBootloaderInput {
                fact_topologies_path: None,
                single_page: false,
                tasks: vec![],
            },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: Felt252::from(1234),
                supported_cairo_verifier_program_hashes: vec![
                    Felt252::from(5678),
                    Felt252::from(8765),
                ],
            },
            packed_outputs: vec![],
        }
    }

    #[rstest]
    fn test_prepare_simple_bootloader_output_segment(bootloader_input: BootloaderInput) {
        let mut vm = VirtualMachine::new(false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(1);

        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin.clone()));

        let mut exec_scopes = ExecutionScopes::new();
        let ids_data = HashMap::from([(
            "simple_bootloader_output_start".to_string(),
            HintReference::new_simple(-1),
        )]);
        let ap_tracking = ApTracking::new();

        exec_scopes.insert_value(vars::BOOTLOADER_INPUT, bootloader_input);
        prepare_simple_bootloader_output_segment(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
        )
        .expect("Hint failed unexpectedly");

        let current_output_builtin = vm
            .get_output_builtin_mut()
            .expect("The VM should have an output builtin")
            .clone();
        let stored_output_builtin: OutputBuiltinState = exec_scopes
            .get(vars::OUTPUT_BUILTIN_STATE)
            .expect("The output builtin is not stored in the execution scope as expected");

        // Check the content of the stored output builtin
        assert_ne!(current_output_builtin.base(), stored_output_builtin.base);
        assert_eq!(stored_output_builtin.base, output_builtin.base());

        let simple_bootloader_output_start = get_maybe_relocatable_from_var_name(
            "simple_bootloader_output_start",
            &vm,
            &ids_data,
            &ap_tracking,
        )
        .expect("Simple bootloader output start not accessible from program IDs");
        assert!(
            matches!(simple_bootloader_output_start, MaybeRelocatable::RelocatableValue(relocatable) if relocatable.segment_index == current_output_builtin.base() as isize)
        );
    }

    #[test]
    fn test_prepare_simple_bootloader_output_segment_missing_input() {
        let mut vm = vm!();
        let mut exec_scopes = ExecutionScopes::new();
        let ids_data = HashMap::<String, HintReference>::new();
        let ap_tracking = ApTracking::default();

        let result = prepare_simple_bootloader_output_segment(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
        );
        let hint_error =
            result.expect_err("Hint should fail, the bootloader input variable is not set");
        assert!(
            matches!(hint_error, HintError::VariableNotInScopeError(s) if s == vars::BOOTLOADER_INPUT.into())
        );
    }
    #[rstest]
    fn test_prepare_simple_bootloader_input(bootloader_input: BootloaderInput) {
        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(vars::BOOTLOADER_INPUT, bootloader_input.clone());

        prepare_simple_bootloader_input(&mut exec_scopes).expect("Hint failed unexpectedly");

        let simple_bootloader_input: SimpleBootloaderInput = exec_scopes
            .get(vars::SIMPLE_BOOTLOADER_INPUT)
            .expect("Simple bootloader input not in scope");
        assert_eq!(
            simple_bootloader_input,
            bootloader_input.simple_bootloader_input
        );
    }

    #[test]
    fn test_restore_bootloader_output() {
        let mut vm: VirtualMachine = vm!();
        // The VM must have an existing output segment
        vm.add_memory_segment();
        vm.builtin_runners = vec![OutputBuiltinRunner::new(true).into()];

        let mut exec_scopes = ExecutionScopes::new();
        let new_segment = vm.add_memory_segment();
        let output_builtin_state = OutputBuiltinState {
            base: new_segment.segment_index.try_into().unwrap(),
            pages: Default::default(),
            attributes: Default::default(),
        };
        exec_scopes.insert_value(vars::OUTPUT_BUILTIN_STATE, output_builtin_state.clone());

        restore_bootloader_output(&mut vm, &mut exec_scopes).expect("Error while executing hint");

        assert_eq!(vm.builtin_runners.len(), 1);
        match &vm.builtin_runners[0] {
            BuiltinRunner::Output(output_builtin) => {
                assert_eq!(output_builtin.base(), output_builtin_state.base);
            }
            other => panic!("Expected an output builtin, found {:?}", other),
        }
    }

    #[rstest]
    fn test_load_bootloader_config(bootloader_input: BootloaderInput) {
        let config = bootloader_input.bootloader_config.clone();

        let mut vm = vm!();
        add_segments!(vm, 2);
        vm.set_fp(2);

        let mut exec_scopes = ExecutionScopes::new();
        let ids_data = ids_data!["bootloader_config"];
        let ap_tracking = ApTracking::new();

        exec_scopes.insert_value(vars::BOOTLOADER_INPUT, bootloader_input);

        load_bootloader_config(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Bootloader hint failed unexpectedly");

        let bootloader_config_segment =
            get_ptr_from_var_name("bootloader_config", &mut vm, &ids_data, &ap_tracking).unwrap();
        let config_segment = vm
            .get_continuous_range(bootloader_config_segment, 3)
            .unwrap();

        // Assert that the values in the config segment match
        let bootloader_hash = &config_segment[0];
        assert!(
            matches!(bootloader_hash, MaybeRelocatable::Int(x) if *x == config.simple_bootloader_program_hash)
        );

        let nb_programs = &config_segment[1];
        let expected_nb_programs = config.supported_cairo_verifier_program_hashes.len();
        assert!(
            matches!(nb_programs, MaybeRelocatable::Int(x) if x.to_usize().unwrap() == expected_nb_programs)
        );

        // Assert that the values in the programs segment match
        let programs_segment = &config_segment[2];
        match programs_segment {
            MaybeRelocatable::RelocatableValue(relocatable) => {
                let program_hashes: Vec<Felt252> = vm
                    .get_integer_range(relocatable.clone(), expected_nb_programs)
                    .unwrap()
                    .iter()
                    .map(|cow| cow.clone().into_owned())
                    .collect();

                assert_eq!(
                    program_hashes,
                    config.supported_cairo_verifier_program_hashes
                );
            }
            other => {
                panic!("Expected a pointer to another segment, got {:?}", other);
            }
        }
    }

    #[rstest]
    fn test_gen_arg() {
        use std::ops::Add;
        let mut vm = vm!();

        let mut nested_args = Vec::<Box<dyn Any>>::new();
        nested_args.push(Box::new(MaybeRelocatable::from(128)));
        nested_args.push(Box::new(MaybeRelocatable::from(42)));

        let mut args = Vec::<Box<dyn Any>>::new();
        args.push(Box::new(MaybeRelocatable::from(1001)));
        args.push(Box::new(MaybeRelocatable::from(2048)));
        args.push(Box::new(nested_args));

        let args_base: Relocatable = gen_arg(&mut vm, &args).expect("gen_args failed unexpectedly");

        let values = vm
            .get_integer_range(args_base, 2)
            .expect("Loading values failed");

        assert_eq!(*values[0], 1001.into());
        assert_eq!(*values[1], 2048.into());

        let nested_args_address: Relocatable = args_base.add(2i32).unwrap();
        let nested_args_base = vm
            .get_relocatable(nested_args_address)
            .expect("Nested vector should be here");

        let nested_values = vm
            .get_integer_range(nested_args_base, 2)
            .expect("Loading nested values failed");

        assert_eq!(*nested_values[0], 128.into());
        assert_eq!(*nested_values[1], 42.into());
    }

    #[rstest]
    fn test_enter_packed_output_scope() {
        let mut vm = vm!();
        // Set n_subtasks to 2
        vm.set_fp(1);
        define_segments!(vm, 2, [((1, 0), 2)]);
        // let ids_data = ids_data!["n_subtasks"];
        let ids_data = HashMap::from([("n_subtasks".to_string(), HintReference::new_simple(-1))]);
        dbg!(&ids_data);
        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        let packed_outputs = vec![
            PackedOutput::Plain(vec![]),
            PackedOutput::Composite(CompositePackedOutput::default()),
            PackedOutput::Plain(vec![]),
        ];
        exec_scopes.insert_value(vars::PACKED_OUTPUTS, packed_outputs);

        enter_packed_output_scope(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that we entered a new scope
        assert_eq!(exec_scopes.data.len(), 2);
        assert_eq!(exec_scopes.data[1].len(), 1);

        let packed_output = exec_scopes
            .get(vars::PACKED_OUTPUT)
            .expect("PACKED_OUTPUT not present in scope");

        assert!(matches!(packed_output, PackedOutput::Composite(_)));
    }

    #[test]
    fn test_is_plain_packed_output() {
        let mut vm = vm!();
        add_segments!(vm, 2);

        let mut exec_scopes = ExecutionScopes::new();

        fn is_plain(
            vm: &mut VirtualMachine,
            exec_scopes: &mut ExecutionScopes,
            packed_output: PackedOutput,
        ) -> bool {
            exec_scopes.insert_value(vars::PACKED_OUTPUT, packed_output);
            is_plain_packed_output(vm, exec_scopes).expect("Hint failed unexpectedly");
            let result = vm.get_integer(vm.get_ap()).unwrap();

            result.into_owned() != Felt252::from(0)
        }

        let plain_packed_output = PackedOutput::Plain(Vec::<Felt252>::new());
        let composite_packed_output = PackedOutput::Composite(CompositePackedOutput::default());

        assert!(is_plain(&mut vm, &mut exec_scopes, plain_packed_output));

        // Increment AP to avoid an inconsistent memory error writing in the same slot
        let new_ap = (*&vm.get_ap() + 1usize).unwrap();
        vm.set_ap(new_ap.offset);
        assert!(!is_plain(
            &mut vm,
            &mut exec_scopes,
            composite_packed_output
        ));
    }

    #[test]
    fn test_save_output_pointer() {
        let mut vm = vm!();
        define_segments!(vm, 2, [((1, 0), (0, 0))]);
        let mut hint_ref = HintReference::new(0, 0, true, false);
        hint_ref.offset2 = OffsetValue::Value(2);
        let ids_data = HashMap::from([("output_ptr".to_string(), hint_ref)]);

        let mut exec_scopes = ExecutionScopes::new();

        let hint_data =
            HintProcessorData::new_default(String::from(BOOTLOADER_SAVE_OUTPUT_POINTER), ids_data);
        let mut hint_processor = MinimalBootloaderHintProcessor::new();
        assert_matches!(
            hint_processor.execute_hint(
                &mut vm,
                &mut exec_scopes,
                &any_box!(hint_data),
                &HashMap::new(),
            ),
            Ok(())
        );

        let output_ptr = exec_scopes.get::<Relocatable>("output_start");
        assert_matches!(
            output_ptr,
            Ok(x) if x == relocatable!(0, 2)
        );
    }

    #[test]
    fn test_save_packed_outputs() {
        let packed_outputs = vec![
            PackedOutput::Plain(Default::default()),
            PackedOutput::Plain(Default::default()),
            PackedOutput::Plain(Default::default()),
        ];

        let bootloader_input = BootloaderInput {
            simple_bootloader_input: SimpleBootloaderInput {
                fact_topologies_path: None,
                single_page: false,
                tasks: vec![],
            },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: 42u64.into(),
                supported_cairo_verifier_program_hashes: Default::default(),
            },
            packed_outputs: packed_outputs.clone(),
        };

        let mut vm = vm!();
        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_box("bootloader_input", Box::new(bootloader_input.clone()));

        let hint_data = HintProcessorData::new_default(
            String::from(BOOTLOADER_SAVE_PACKED_OUTPUTS),
            HashMap::new(),
        );
        let mut hint_processor = MinimalBootloaderHintProcessor::new();
        assert_matches!(
            hint_processor.execute_hint(
                &mut vm,
                &mut exec_scopes,
                &any_box!(hint_data),
                &HashMap::new(),
            ),
            Ok(())
        );

        let saved_packed_outputs = exec_scopes.get::<Vec<PackedOutput>>("packed_outputs");
        assert_matches!(
            saved_packed_outputs,
            Ok(ref x) if x == &packed_outputs
        );

        assert_eq!(
            saved_packed_outputs.expect("asserted Ok above, qed").len(),
            3
        );
    }

    #[rstest]
    fn test_compute_and_configure_fact_topologies(bootloader_input: BootloaderInput) {
        let mut vm = vm!();
        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin.clone()));

        let mut exec_scopes = ExecutionScopes::new();
        let packed_outputs = vec![PackedOutput::Plain(vec![]), PackedOutput::Plain(vec![])];
        let fact_topologies = vec![
            FactTopology {
                tree_structure: vec![],
                page_sizes: vec![3usize, 1usize],
            },
            FactTopology {
                tree_structure: vec![],
                page_sizes: vec![10usize],
            },
        ];
        let output_start = Relocatable {
            segment_index: output_builtin.base() as isize,
            offset: 0,
        };
        exec_scopes.insert_value(vars::BOOTLOADER_INPUT, bootloader_input);
        exec_scopes.insert_value(vars::PACKED_OUTPUTS, packed_outputs);
        exec_scopes.insert_value(vars::FACT_TOPOLOGIES, fact_topologies);
        exec_scopes.insert_value(vars::OUTPUT_START, output_start);

        compute_and_configure_fact_topologies(&mut vm, &mut exec_scopes)
            .expect("Hint failed unexpectedly");

        let output_start: Relocatable = exec_scopes.get(vars::OUTPUT_START).unwrap();
        assert_eq!(
            output_start,
            Relocatable {
                segment_index: 0,
                offset: 18
            }
        );
        let pages = match vm.get_output_builtin_mut().unwrap().get_additional_data() {
            cairo_vm::vm::runners::cairo_pie::BuiltinAdditionalData::Output(o) => o.pages,
            _ => unreachable!("Type should be Output"),
        };

        assert_eq!(
            pages,
            HashMap::from([
                (1, PublicMemoryPage { start: 2, size: 3 }),
                (2, PublicMemoryPage { start: 5, size: 1 }),
                (3, PublicMemoryPage { start: 8, size: 10 }),
            ])
        );
    }

    #[test]
    fn test_set_packed_output_to_subtasks() {
        let mut vm = vm!();
        let mut exec_scopes = ExecutionScopes::new();

        let subtasks = vec![
            PackedOutput::Plain(vec![]),
            PackedOutput::Composite(CompositePackedOutput::default()),
        ];
        exec_scopes.insert_value(
            vars::PACKED_OUTPUT,
            PackedOutput::Composite(CompositePackedOutput {
                outputs: vec![],
                subtasks: subtasks.clone(),
            }),
        );

        let hint_data = HintProcessorData::new_default(
            String::from(BOOTLOADER_SET_PACKED_OUTPUT_TO_SUBTASKS),
            HashMap::new(),
        );
        let mut hint_processor = MinimalBootloaderHintProcessor::new();
        assert_matches!(
            hint_processor.execute_hint(
                &mut vm,
                &mut exec_scopes,
                &any_box!(hint_data),
                &HashMap::new(),
            ),
            Ok(())
        );

        let packed_outputs: Vec<PackedOutput> = exec_scopes.get(vars::PACKED_OUTPUTS).unwrap();
        assert_eq!(packed_outputs, subtasks);
    }

    #[test]
    fn test_guess_pre_image_of_subtasks_output_hash() {
        let mut vm = vm!();
        add_segments!(vm, 2);
        vm.set_fp(2);

        let ids_data = ids_data!["nested_subtasks_output_len", "nested_subtasks_output"];

        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_box(
            "packed_output",
            Box::new(PackedOutput::Composite(CompositePackedOutput {
                outputs: vec![Felt252::from(42)],
                subtasks: vec![],
            })),
        );

        let ap_tracking = ApTracking::new();

        assert_matches!(
            run_hint!(
                vm,
                ids_data.clone(),
                BOOTLOADER_GUESS_PRE_IMAGE_OF_SUBTASKS_OUTPUT_HASH,
                &mut exec_scopes
            ),
            Ok(())
        );
        let nested_subtasks_output_len =
            get_integer_from_var_name("nested_subtasks_output_len", &vm, &ids_data, &ap_tracking)
                .expect("nested_subtasks_output_len should be set")
                .to_owned();
        assert_eq!(nested_subtasks_output_len, 1.into());

        let nested_subtasks_output =
            get_ptr_from_var_name("nested_subtasks_output", &vm, &ids_data, &ap_tracking)
                .expect("nested_subtasks_output should be set");
        let arg = vm.get_integer(nested_subtasks_output).unwrap().into_owned();
        assert_eq!(arg, Felt252::from(42));
    }

    #[rstest]
    fn test_assert_is_composite_packed_output() {
        let mut exec_scopes = ExecutionScopes::new();

        let plain_packed_output = PackedOutput::Plain(Vec::<Felt252>::new());
        exec_scopes.insert_value(vars::PACKED_OUTPUT, plain_packed_output);
        assert!(matches!(
            assert_is_composite_packed_output(&mut exec_scopes),
            Err(HintError::CustomHint(_))
        ));

        let composite_packed_output = PackedOutput::Composite(CompositePackedOutput::default());
        exec_scopes.insert_value(vars::PACKED_OUTPUT, composite_packed_output);
        assert!(assert_is_composite_packed_output(&mut exec_scopes).is_ok());
    }

    #[rstest]
    #[case(false)]
    #[case(true)]
    fn test_assert_program_address(#[case] expect_fail: bool) {
        let mut vm = vm!();

        add_segments!(vm, 2);
        vm.set_fp(2);

        let ids_data = ids_data!(vars::PROGRAM_ADDRESS);
        let ap_tracking = ApTracking::new();

        let mut ptr = Relocatable {
            segment_index: 42,
            offset: 42,
        };
        let _ = insert_value_from_var_name(
            vars::PROGRAM_ADDRESS,
            ptr.clone(),
            &mut vm,
            &ids_data,
            &ap_tracking,
        )
        .map_err(|e| panic!("could not insert var: {}", e));

        if expect_fail {
            ptr = Relocatable {
                segment_index: 1,
                offset: 1,
            };
        }

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_box(vars::PROGRAM_ADDRESS, any_box!(ptr));

        let result = run_hint!(
            vm,
            ids_data.clone(),
            EXECUTE_TASK_ASSERT_PROGRAM_ADDRESS,
            &mut exec_scopes
        );

        match result {
            Ok(_) => assert!(!expect_fail),
            Err(HintError::CustomHint(e)) => {
                assert!(expect_fail);
                assert_eq!(e.as_ref(), "program address is incorrect");
                ()
            }
            _ => panic!("result not recognized"),
        }
    }
}
