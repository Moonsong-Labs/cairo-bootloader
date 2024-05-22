use std::any::Any;
use std::collections::HashMap;

use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::get_integer_from_var_name;
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::errors::math_errors::MathError;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::vm_core::VirtualMachine;
use num_traits::ToPrimitive;

use crate::hints::vars;

/// Implements
/// %{ vm_enter_scope({'n_selected_builtins': ids.n_selected_builtins}) %}
pub fn select_builtins_enter_scope(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let n_selected_builtins =
        get_integer_from_var_name(vars::N_SELECTED_BUILTINS, vm, ids_data, ap_tracking)?;
    let n_selected_builtins =
        n_selected_builtins
            .to_usize()
            .ok_or(MathError::Felt252ToUsizeConversion(Box::new(
                n_selected_builtins,
            )))?;

    exec_scopes.enter_scope(HashMap::from([(
        vars::N_SELECTED_BUILTINS.to_string(),
        Box::new(n_selected_builtins) as Box<dyn Any>,
    )]));

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::any::Any;
    use std::collections::HashMap;

    use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::get_integer_from_var_name;
    use cairo_vm::hint_processor::hint_processor_definition::HintReference;
    use cairo_vm::serde::deserialize_program::ApTracking;
    use cairo_vm::types::exec_scope::ExecutionScopes;
    use cairo_vm::vm::errors::hint_errors::HintError;
    use cairo_vm::vm::vm_core::VirtualMachine;
    use num_traits::ToPrimitive;
    use serde::Serialize;

    use super::*;

    #[test]
    fn test_select_builtins_enter_scope() {
        let mut vm = vm!();
        // Set n_selected_builtins to 7
        vm.run_context.fp = 1;
        vm.segments = segments![((1, 0), 7)];
        let ids_data = ids_data![vars::N_SELECTED_BUILTINS];
        let n_selected_builtins = 7usize;

        let ap_tracking = ApTracking::default();
        let mut exec_scopes = ExecutionScopes::new();

        select_builtins_enter_scope(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that we entered a new scope
        assert_eq!(exec_scopes.data.len(), 2);
        assert_eq!(exec_scopes.data[1].len(), 1);

        let n_selected_builtins_var: usize = exec_scopes.get(vars::N_SELECTED_BUILTINS).unwrap();

        assert_eq!(n_selected_builtins_var, n_selected_builtins);
    }
}
