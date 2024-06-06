#[macro_export]
macro_rules! vm {
    () => {
        VirtualMachine::new(false) // Default to false if no argument is provided
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
    ( $( $key:expr ),* ) => {{
        let mut map = HashMap::<String, cairo_vm::hint_processor::hint_processor_definition::HintReference>::new();
        let ids_names = vec![$( $key ),*];
        let ids_len = ids_names.len() as i32;
        let mut _value = -ids_len;
        $(
            map.insert($key.to_string(), cairo_vm::hint_processor::hint_processor_definition::HintReference::new_simple(_value));
            _value += 1;
        )*
        map
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
macro_rules! insert_value_inner {
    ($vm:expr, ($si:expr, $off:expr), ($sival:expr, $offval: expr)) => {
        let (k, v) = (
            ($si, $off).into(),
            &$crate::mayberelocatable!($sival, $offval),
        );
        $vm.insert_value(k, v).unwrap();
    };
    ($vm:expr, ($si:expr, $off:expr), $val:expr) => {
        let (k, v) = (($si, $off).into(), &$crate::mayberelocatable!($val));
        $vm.insert_value(k, v).unwrap();
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

#[macro_export]
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
            $crate::stdlib::string::ToString::to_string($hint_code),
            $ids_data,
        );
        let mut hint_processor = $crate::MinimalBootloaderHintProcessor::new();
        hint_processor.execute_hint(
            &mut $vm,
            exec_scopes_ref!(),
            &any_box!(hint_data),
            &$crate::stdlib::collections::HashMap::new(),
        )
    }};
}
