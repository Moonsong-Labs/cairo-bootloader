use cairo_vm::types::builtin_name::BuiltinName;
use cairo_vm::types::errors::math_errors::MathError;
use cairo_vm::types::relocatable::Relocatable;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::errors::memory_errors::MemoryError;
use cairo_vm::vm::runners::cairo_pie::StrippedProgram;
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::Felt252;

use crate::hints::types::BootloaderVersion;

#[derive(thiserror_no_std::Error, Debug)]
pub enum ProgramLoaderError {
    #[error(transparent)]
    Math(#[from] MathError),

    #[error(transparent)]
    Memory(#[from] MemoryError),
}

impl From<ProgramLoaderError> for HintError {
    fn from(value: ProgramLoaderError) -> Self {
        match value {
            ProgramLoaderError::Math(e) => HintError::Math(e),
            ProgramLoaderError::Memory(e) => HintError::Memory(e),
        }
    }
}

/// Creates an instance of `Felt252` from a builtin name.
///
/// Converts the builtin name to bytes then attempts to create a felt from
/// these bytes. This function will fail if the builtin name is over 31 characters.
///
/// This is used by the loader to make the builtins used by the program to the Cairo
/// code.
fn builtin_to_felt(builtin: &BuiltinName) -> Result<Felt252, ProgramLoaderError> {
    // The Python implementation uses the builtin name without suffix
    let builtin_name = builtin.to_str();

    Ok(Felt252::from_bytes_be_slice(builtin_name.as_bytes()))
}

pub struct LoadedProgram {
    /// Start of the program code in the VM memory.
    pub code_address: Relocatable,
    /// Total size of the program in memory, header included.
    pub size: usize,
}

/// Loads a Cairo program in the VM memory.
pub struct ProgramLoader<'vm> {
    /// Memory accessor.
    vm: &'vm mut VirtualMachine,
    /// Offset of the builtin list array in the Cairo VM memory.
    builtins_offset: usize,
}

impl<'vm> ProgramLoader<'vm> {
    pub fn new(vm: &'vm mut VirtualMachine, builtins_offset: usize) -> Self {
        Self {
            vm,
            builtins_offset,
        }
    }

    fn load_builtins(
        &mut self,
        builtin_list_ptr: Relocatable,
        builtins: &[BuiltinName],
    ) -> Result<(), ProgramLoaderError> {
        for (index, builtin) in builtins.iter().enumerate() {
            let builtin_felt = builtin_to_felt(builtin)?;
            self.vm
                .insert_value((builtin_list_ptr + index)?, builtin_felt)?;
        }

        Ok(())
    }

    fn load_header(
        &mut self,
        base_address: Relocatable,
        program: &StrippedProgram,
        bootloader_version: Option<BootloaderVersion>,
    ) -> Result<usize, ProgramLoaderError> {
        // Map the header struct as memory addresses
        let data_length_ptr = base_address;
        let bootloader_version_ptr = (base_address + 1)?;
        let program_main_ptr = (base_address + 2)?;
        let n_builtins_ptr = (base_address + 3)?;
        let builtin_list_ptr = (base_address + 4)?;

        let program_data = &program.data;

        let builtins = &program.builtins;
        let n_builtins = builtins.len();
        let header_size = self.builtins_offset + n_builtins;

        // data_length does not include the data_length header field in the calculation.
        let data_length = header_size - 1 + program_data.len();
        let program_main = program.main;

        let bootloader_version = bootloader_version.unwrap_or(0);

        self.vm.insert_value(data_length_ptr, data_length)?;
        self.vm
            .insert_value(bootloader_version_ptr, Felt252::from(bootloader_version))?;
        self.vm.insert_value(program_main_ptr, program_main)?;
        self.vm.insert_value(n_builtins_ptr, n_builtins)?;

        self.load_builtins(builtin_list_ptr, builtins)?;

        Ok(header_size)
    }

    fn load_code(
        &mut self,
        base_address: Relocatable,
        program: &StrippedProgram,
    ) -> Result<(), ProgramLoaderError> {
        for (index, opcode) in program.data.iter().enumerate() {
            self.vm.insert_value((base_address + index)?, opcode)?;
        }

        Ok(())
    }

    /// Loads a Cairo program in the VM memory.
    ///
    /// Programs are loaded in two parts:
    /// 1. The program header contains metadata (ex: entrypoint, program size,
    ///    builtins used by the program).
    /// 2. The program itself.
    ///
    /// Starting from `base_address`, the header contains the following fields:
    /// 1. The size of the header
    /// 2. The bootloader version
    /// 3. The program entrypoint
    /// 4. The number of builtins used by the program
    /// 5. The list of builtins used (converted to felts) as a C-style array.
    ///
    /// * `base_address`: Where to load the program, see above.
    /// * `program`: The program to load.
    /// * `bootloader_version`: The bootloader version. Defaults to 0.
    ///
    /// Returns the address where the code of the program is loaded and the program size.
    pub fn load_program(
        &mut self,
        base_address: Relocatable,
        program: &StrippedProgram,
        bootloader_version: Option<BootloaderVersion>,
    ) -> Result<LoadedProgram, ProgramLoaderError> {
        let header_size = self.load_header(base_address, program, bootloader_version)?;

        let program_address = (base_address + header_size)?;
        self.load_code(program_address, program)?;

        Ok(LoadedProgram {
            code_address: program_address,
            size: header_size + program.data.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    

    use cairo_vm::types::builtin_name::BuiltinName;
    use cairo_vm::types::program::Program;
    use cairo_vm::types::relocatable::Relocatable;
    use cairo_vm::vm::runners::cairo_pie::StrippedProgram;
    use cairo_vm::vm::vm_memory::memory_segments::MemorySegmentManager;
    use cairo_vm::Felt252;
    
    use rstest::{fixture, rstest};
    

    use crate::{add_segments, hints::types::BootloaderVersion};

    use super::*;

    #[rstest]
    #[case::output(BuiltinName::output, 122550255383924)]
    #[case::pedersen(BuiltinName::pedersen, 8098989891770344814)]
    fn test_builtin_to_felt(#[case] builtin_name: BuiltinName, #[case] expected_value: u64) {
        let expected_felt = Felt252::from(expected_value);
        let felt = builtin_to_felt(&builtin_name).unwrap();

        assert_eq!(felt, expected_felt);
    }

    fn check_loaded_builtins(
        vm: &VirtualMachine,
        builtins: &[&str],
        builtin_list_ptr: Relocatable,
    ) {
        let builtin_felts = vm
            .get_integer_range(builtin_list_ptr, builtins.len())
            .expect("Builtins not loaded properly in memory");
        for (builtin, felt) in std::iter::zip(vec!["bitwise", "output", "pedersen"], builtin_felts)
        {
            let builtin_from_felt = String::from_utf8(felt.into_owned().to_bytes_be().to_vec())
                .expect(
                    format!(
                        "Could not decode builtin from memory (expected {})",
                        builtin
                    )
                    .as_ref(),
                );
            // Compare the last N characters, builtin_from_felt is padded left with zeroes
            assert_eq!(&builtin_from_felt[32 - builtin.len()..32], builtin);
        }
    }

    #[test]
    fn test_load_builtins() {
        let builtins = vec![
            BuiltinName::bitwise,
            BuiltinName::output,
            BuiltinName::pedersen,
        ];

        let mut vm = VirtualMachine::new(false);
        let builtin_list_ptr = vm.add_memory_segment();

        let builtins_offset = 4;
        let mut program_loader = ProgramLoader::new(&mut vm, builtins_offset);

        program_loader
            .load_builtins(builtin_list_ptr, &builtins)
            .expect("Failed to load builtins in memory");

        check_loaded_builtins(
            &vm,
            &vec!["bitwise", "output", "pedersen"],
            builtin_list_ptr,
        );
    }

    #[fixture]
    fn fibonacci() -> Program {
        let program_content =
            include_bytes!("/home/geoff/Desktop/test-cairo/fibonacci.json").to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    fn check_loaded_header(
        vm: &VirtualMachine,
        header_address: Relocatable,
        program: &StrippedProgram,
        bootloader_version: BootloaderVersion,
    ) {
        let header_felts = vm.get_integer_range(header_address, 4).unwrap();
        let expected_data_length = program.data.len() + 3;
        let program_main = program.main;
        let n_builtins = program.builtins.len();

        assert_eq!(
            header_felts[0].clone().into_owned(),
            Felt252::from(expected_data_length)
        );
        assert_eq!(
            header_felts[1].clone().into_owned(),
            Felt252::from(bootloader_version)
        );
        assert_eq!(
            header_felts[2].clone().into_owned(),
            Felt252::from(program_main)
        );
        assert_eq!(
            header_felts[3].clone().into_owned(),
            Felt252::from(n_builtins)
        );
    }

    #[rstest]
    fn test_load_header(fibonacci: Program) {
        let program = fibonacci.get_stripped_program().unwrap();

        let mut vm = VirtualMachine::new(false);
        add_segments!(vm, 2);
        let mut segments = MemorySegmentManager::new();
        let base_address = segments.add();

        let builtins_offset = 4;
        let mut program_loader = ProgramLoader::new(&mut vm, builtins_offset);

        let bootloader_version: BootloaderVersion = 0;
        program_loader
            .load_header(base_address, &program, Some(bootloader_version))
            .expect("Failed to load program header in memory");

        check_loaded_header(&vm, base_address.clone(), &program, bootloader_version);

        let builtin_list_ptr = (base_address + builtins_offset).unwrap();
        check_loaded_builtins(&vm, &vec![], builtin_list_ptr);
    }

    fn check_loaded_program(
        vm: &VirtualMachine,
        code_address: Relocatable,
        program: &StrippedProgram,
    ) {
        let loaded_opcodes = vm
            .get_continuous_range(code_address, program.data.len())
            .expect("Program not loaded properly in memory");

        for (loaded, original) in std::iter::zip(loaded_opcodes, &program.data) {
            assert_eq!(loaded, *original);
        }
    }

    #[rstest]
    fn test_load_program(fibonacci: Program) {
        let program = fibonacci.get_stripped_program().unwrap();

        let mut vm = VirtualMachine::new(false);
        add_segments!(vm, 2);
        let mut segments = MemorySegmentManager::new();
        let base_address = segments.add();

        let builtins_offset = 4;
        let mut program_loader = ProgramLoader::new(&mut vm, builtins_offset);

        let bootloader_version: BootloaderVersion = 0;
        let loaded_program = program_loader
            .load_program(base_address, &program, Some(bootloader_version))
            .expect("Failed to load program in memory");

        let header_size = builtins_offset + program.builtins.len();
        let expected_code_address = (base_address + header_size).unwrap();
        assert_eq!(loaded_program.code_address, expected_code_address);

        assert_eq!(loaded_program.size, header_size + program.data.len());

        check_loaded_program(&vm, loaded_program.code_address, &program);

        check_loaded_header(&vm, base_address.clone(), &program, bootloader_version);

        let builtin_list_ptr = (base_address + builtins_offset).unwrap();
        check_loaded_builtins(&vm, &vec![], builtin_list_ptr);
    }
}
