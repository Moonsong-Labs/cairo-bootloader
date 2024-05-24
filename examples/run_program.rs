use std::any::Any;
use std::collections::HashMap;
use std::error::Error;

use cairo_vm::cairo_run::{cairo_run_program, CairoRunConfig};
use cairo_vm::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::{
    BuiltinHintProcessor, HintProcessorData,
};
use cairo_vm::hint_processor::hint_processor_definition::{HintExtension, HintProcessorLogic};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::runners::cairo_runner::{CairoRunner, ResourceTracker};
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::Felt252;
use starknet_types_core::felt::Felt;

use cairo_bootloader::tasks::make_bootloader_tasks;
use cairo_bootloader::{
    insert_bootloader_input, load_bootloader, BootloaderConfig, BootloaderHintProcessor,
    BootloaderInput, PackedOutput, SimpleBootloaderInput, TaskSpec,
};

struct ExampleHintProcessor {
    bootloader_hint_processor: BootloaderHintProcessor,
    builtin_hint_processor: BuiltinHintProcessor,
}

impl ExampleHintProcessor {
    fn new() -> Self {
        Self {
            bootloader_hint_processor: BootloaderHintProcessor {},
            builtin_hint_processor: BuiltinHintProcessor::new_empty(),
        }
    }
}

impl HintProcessorLogic for ExampleHintProcessor {
    fn execute_hint(
        &mut self,
        _vm: &mut VirtualMachine,
        _exec_scopes: &mut ExecutionScopes,
        hint_data: &Box<dyn Any>,
        _constants: &HashMap<String, Felt>,
    ) -> Result<(), HintError> {
        // This method will never be called, but must be defined according to `HintProcessorLogic`.

        let hint_data = hint_data.downcast_ref::<HintProcessorData>().unwrap();
        let hint_code = &hint_data.code;
        Err(HintError::UnknownHint(hint_code.clone().into_boxed_str()))
    }

    fn execute_hint_extensive(
        &mut self,
        vm: &mut VirtualMachine,
        exec_scopes: &mut ExecutionScopes,
        hint_data: &Box<dyn Any>,
        constants: &HashMap<String, Felt>,
    ) -> Result<HintExtension, HintError> {
        // Cascade through the internal hint processors until we find the hint implementation.

        match self.bootloader_hint_processor.execute_hint_extensive(
            vm,
            exec_scopes,
            hint_data,
            constants,
        ) {
            Err(HintError::UnknownHint(_)) => {}
            result => {
                return result;
            }
        }

        self.builtin_hint_processor
            .execute_hint_extensive(vm, exec_scopes, hint_data, constants)
    }
}

impl ResourceTracker for ExampleHintProcessor {}

fn cairo_run_bootloader_in_proof_mode(
    bootloader_program: &Program,
    tasks: Vec<TaskSpec>,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = ExampleHintProcessor::new();

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

    let _runner = cairo_run_bootloader_in_proof_mode(&bootloader_program, tasks)?;

    Ok(())
}
