use cairo_vm::types::exec_scope::ExecutionScopes;
pub use hints::*;

pub mod bootloaders;
mod hints;
pub mod tasks;

/// Inserts the bootloader input in the execution scopes.
pub fn insert_bootloader_input(
    exec_scopes: &mut ExecutionScopes,
    bootloader_input: BootloaderInput,
) {
    exec_scopes.insert_value(BOOTLOADER_INPUT, bootloader_input);
}

#[macro_export]
macro_rules! vm {
    () => {
        VirtualMachine::new(false) // Default to false if no argument is provided
    };
    ($trace_enabled:expr) => {
        VirtualMachine::new($trace_enabled)
    };
}

#[macro_export]
macro_rules! add_segments {
    ($vm:expr, $n:expr) => {
        for _ in 0..$n {
            $vm.add_memory_segment();
        }
    };
}
#[macro_export]
macro_rules! ids_data {
    ( $( $name: expr ),* ) => {
        {
            #[allow(clippy::useless_vec)]
            let ids_names = vec![$( $name ),*];
            let references = $crate::references!(ids_names.len() as i32);
            let mut ids_data = HashMap::<String, cairo_vm::hint_processor::hint_processor_definition::HintReference>::new();
            for (i, name) in ids_names.iter().enumerate() {
                ids_data.insert(name.to_string(), references.get(&i).unwrap().clone());
            }
            ids_data
        }
    };
}
#[macro_export]
macro_rules! references {
    ($num: expr) => {{
        let mut references = HashMap::<
            usize,
            cairo_vm::hint_processor::hint_processor_definition::HintReference,
        >::new();
        for i in 0..$num {
            references.insert(
                i as usize,
                cairo_vm::hint_processor::hint_processor_definition::HintReference::new_simple(
                    (i as i32),
                ),
            );
        }
        references
    }};
}

#[macro_export]
macro_rules! non_continuous_ids_data {
    ( $( ($name: expr, $offset:expr) ),* $(,)? ) => {
        {
            let mut ids_data = cairo_vm::stdlib::collections::HashMap::<cairo_vm::stdlib::string::String, HintReference>::new();
            $(
                ids_data.insert(cairo_vm::stdlib::string::String::from($name), HintReference::new_simple($offset));
            )*
            ids_data
        }
    };
}

#[macro_export]
macro_rules! segments {
    ($( (($si:expr, $off:expr), $val:tt) ),* $(,)? ) => {
        {
            let mut segments = cairo_vm::vm::vm_memory::memory_segments::MemorySegmentManager::new();
            segments.memory = $crate::memory!($( (($si, $off), $val) ),*);
            segments
        }

    };
}

#[macro_export]
macro_rules! memory {
    ( $( (($si:expr, $off:expr), $val:tt) ),* ) => {
        {
            let mut memory = cairo_vm::vm::vm_memory::memory::Memory::new();
            $crate::memory_from_memory!(memory, ( $( (($si, $off), $val) ),* ));
            memory
        }
    };
}

#[macro_export]
macro_rules! memory_from_memory {
    ($mem: expr, ( $( (($si:expr, $off:expr), $val:tt) ),* )) => {
        {
            $(
                $crate::memory_inner!($mem, ($si, $off), $val);
            )*
        }
    };
}

#[macro_export]
macro_rules! insert_value_inner {
    ($vm:expr, ($si:expr, $off:expr), ($sival:expr, $offval: expr)) => {
        let (k, v) = (
            ($si, $off).into(),
            &$crate::mayberelocatable!($sival, $offval),
        );
        let mut res = $vm.insert_value(k, v);
        while matches!(
            res,
            Err(cairo_vm::vm::errors::memory_errors::MemoryError::UnallocatedSegment(_))
        ) {
            dbg!(&res);
            if $si < 0 {
                // $vm.temp_data.push(cairo_vm::stdlib::vec::Vec::new())
            } else {
                // $vm.data.push(cairo_vm::stdlib::vec::Vec::new());
            }
            res = $vm.insert_value(k, v);
        }
    };
    ($vm:expr, ($si:expr, $off:expr), $val:expr) => {
        let (k, v) = (($si, $off).into(), &$crate::mayberelocatable!($val));
        let mut res = $vm.insert_value(k, v);
        while matches!(
            res,
            Err(cairo_vm::vm::errors::memory_errors::MemoryError::UnallocatedSegment(_))
        ) {
            dbg!(&res);
            if $si < 0 {
                // $mem.temp_data.push($crate::stdlib::vec::Vec::new())
            } else {
                // $mem.data.push($crate::stdlib::vec::Vec::new());
            }
            res = $vm.insert_value(k, v);
        }
    };
}

#[macro_export]
macro_rules! mayberelocatable {
    ($val1 : expr, $val2 : expr) => {
        cairo_vm::types::relocatable::MaybeRelocatable::from(($val1, $val2))
    };
    ($val1 : expr) => {
        cairo_vm::types::relocatable::MaybeRelocatable::from(cairo_vm::Felt252::from($val1 as i128))
    };
}

#[macro_export]
macro_rules! define_segments {
    ($vm:ident, $count:expr, [$( (($seg1:expr, $off1:expr), $val:tt) ),* $(,)?]) => {
        for _ in 0..$count {
            $vm.add_memory_segment();
        }
        $(
            $crate::insert_value_inner!($vm, ($seg1, $off1), $val);
        )*
    };
}


macro_rules! run_hint {
    ($vm:expr, $ids_data:expr, $hint_code:expr, $exec_scopes:expr, $constants:expr) => {{
        let hint_data = HintProcessorData::new_default($hint_code.to_string(), $ids_data);
        let mut hint_processor = $crate::MinimalBootloaderHintProcessor::new();
        hint_processor.execute_hint(&mut $vm, $exec_scopes, &any_box!(hint_data), $constants)
    }};
    ($vm:expr, $ids_data:expr, $hint_code:expr, $exec_scopes:expr) => {{
        let hint_data = HintProcessorData::new_default(
            cairo_vm::stdlib::string::ToString::to_string($hint_code),
            $ids_data,
        );
        let mut hint_processor = $crate::MinimalBootloaderHintProcessor::new();
        hint_processor.execute_hint(
            &mut $vm,
            $exec_scopes,
            &any_box!(hint_data),
            &cairo_vm::stdlib::collections::HashMap::new(),
        )
    }};
    ($vm:expr, $ids_data:expr, $hint_code:expr) => {{
        let hint_data = HintProcessorData::new_default(
            crate::stdlib::string::ToString::to_string($hint_code),
            $ids_data,
        );
        let mut hint_processor = $crate::MinimalBootloaderHintProcessor::new();
        hint_processor.execute_hint(
            &mut $vm,
            exec_scopes_ref!(),
            &any_box!(hint_data),
            &crate::stdlib::collections::HashMap::new(),
        )
    }};
}
pub(crate) use run_hint;

