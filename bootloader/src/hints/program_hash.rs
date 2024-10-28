use cairo_vm::types::builtin_name::BuiltinName;
use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::vm::runners::cairo_pie::StrippedProgram;
use cairo_vm::Felt252;
use starknet_crypto::{pedersen_hash, Felt};

type HashFunction = fn(&Felt, &Felt) -> Felt;

#[derive(thiserror_no_std::Error, Debug)]
pub enum HashChainError {
    #[error("Data array must contain at least one element.")]
    EmptyData,
}

#[derive(thiserror_no_std::Error, Debug)]
pub enum ProgramHashError {
    #[error(transparent)]
    HashChain(#[from] HashChainError),

    #[error(
        "Invalid program builtin: builtin name too long to be converted to field element: {0}"
    )]
    InvalidProgramBuiltin(&'static str),

    #[error("Invalid program data: data contains relocatable(s)")]
    InvalidProgramData,
}

/// Computes a hash chain over the data, in the following order:
///     h(data[0], h(data[1], h(..., h(data[n-2], data[n-1])))).
///
/// Reimplements this Python function:
/// def compute_hash_chain(data, hash_func=pedersen_hash):
///     assert len(data) >= 1, f"len(data) for hash chain computation must be >= 1; got: {len(data)}."
///     return functools.reduce(lambda x, y: hash_func(y, x), data[::-1])
fn compute_hash_chain<'a, I>(
    data: I,
    hash_func: HashFunction,
) -> Result<Felt, HashChainError>
where
    I: Iterator<Item = &'a Felt> + DoubleEndedIterator,
{
    match data.copied().rev().reduce(|x, y| hash_func(&y, &x)) {
        Some(result) => Ok(result),
        None => Err(HashChainError::EmptyData),
    }
}

/// Creates an instance of `Felt` from a builtin name.
///
/// Converts the builtin name to bytes then attempts to create a field element from
/// these bytes. This function will fail if the builtin name is over 31 characters.
fn builtin_to_field_element(builtin: &BuiltinName) -> Result<Felt, ProgramHashError> {
    // The Python implementation uses the builtin name without suffix
    let builtin_name = builtin.to_str();
    let builtin_bytes = builtin_name.as_bytes();

    if builtin_bytes.len() > 31 {
        return Err(ProgramHashError::InvalidProgramBuiltin(builtin_name));
    }

    let mut bytes = [0u8; 32];
    bytes[32 - builtin_bytes.len()..].copy_from_slice(builtin_bytes);

    Ok(Felt::from_bytes_be(&bytes))
}
/// This function converts a `Felt252` to a `Felt` using a safe, albeit inefficient,
/// method.
fn felt_to_field_element(felt: &Felt252) -> Felt {
    let bytes = felt.to_bytes_be();
    Felt::from_bytes_be(&bytes)
}

/// Converts a `MaybeRelocatable` into a `Felt` value.
///
/// Returns `InvalidProgramData` if `maybe_relocatable` is not an integer
fn maybe_relocatable_to_field_element(
    maybe_relocatable: &MaybeRelocatable,
) -> Result<Felt, ProgramHashError> {
    let felt = maybe_relocatable
        .get_int_ref()
        .ok_or(ProgramHashError::InvalidProgramData)?;
    Ok(felt_to_field_element(felt))
}

/// Computes the Pedersen hash of a program.
///
/// Reimplements this Python function:
/// ```no-run
/// def compute_program_hash_chain(program: ProgramBase, bootloader_version=0):
///     builtin_list = [from_bytes(builtin.encode("ascii")) for builtin in program.builtins]
///     # The program header below is missing the data length, which is later added to the data_chain.
///     program_header = [bootloader_version, program.main, len(program.builtins)] + builtin_list
///     data_chain = program_header + program.data
///  
///     return compute_hash_chain([len(data_chain)] + data_chain)
/// ```
pub fn compute_program_hash_chain(
    program: &StrippedProgram,
    bootloader_version: usize,
) -> Result<Felt, ProgramHashError> {
    let program_main = program.main;
    let program_main = Felt::from(program_main);

    // Convert builtin names to field elements
    let builtin_list: Result<Vec<Felt>, _> = program
        .builtins
        .iter()
        .map(builtin_to_field_element)
        .collect();
    let builtin_list = builtin_list?;

    let program_header = vec![
        Felt::from(bootloader_version),
        program_main,
        Felt::from(program.builtins.len()),
    ];

    let program_data: Result<Vec<_>, _> = program
        .data
        .iter()
        .map(maybe_relocatable_to_field_element)
        .collect();
    let program_data = program_data?;

    let data_chain_len = program_header.len() + builtin_list.len() + program_data.len();
    let data_chain_len_vec = vec![Felt::from(data_chain_len)];

    // Prepare a chain of iterators to feed to the hash function
    let data_chain = [
        &data_chain_len_vec,
        &program_header,
        &builtin_list,
        &program_data,
    ];

    let hash = compute_hash_chain(data_chain.iter().flat_map(|&v| v.iter()), pedersen_hash)?;
    Ok(hash)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use cairo_vm::types::program::Program;
    use rstest::rstest;
    use starknet_crypto::pedersen_hash;

    use super::*;

    #[test]
    fn test_compute_hash_chain() {
        let data: Vec<Felt> = vec![
            Felt::from(1u64),
            Felt::from(2u64),
            Felt::from(3u64),
        ];
        let expected_hash = pedersen_hash(
            &Felt::from(1u64),
            &pedersen_hash(&Felt::from(2u64), &Felt::from(3u64)),
        );
        let computed_hash = compute_hash_chain(data.iter(), pedersen_hash)
            .expect("Hash computation failed unexpectedly");

        assert_eq!(computed_hash, expected_hash);
    }

    #[rstest]
    // Expected hashes generated with `cairo-hash-program`
    #[case::fibonacci(
        "examples/fibonacci.json",
        "0x6fc56a47599a5cc20bb3c6d4c5397f872bb6269f036e383f4c13986d4020952"
    )]
    // #[case::field_arithmetic(
    //     "./dependencies/test-programs/cairo0/field-arithmetic/field_arithmetic.json",
    //     "0xdc5a7432daec36bb707aa9f8cbcd60a2c5a4f5b16dbe7a4b6d96d5bfdd2a43"
    // )]
    // #[case::keccak_copy_inputs(
    //     "./dependencies/test-programs/cairo0/keccak-copy-inputs/keccak_copy_inputs.json",
    //     "0x79e69539b9bbcc863519fb17f864c3439277cd851146f30d1ce0232fb358632"
    // )]
    fn test_compute_program_hash_chain(
        #[case] program_path: PathBuf,
        #[case] expected_program_hash: String,
    ) {
        let program =
            Program::from_file(program_path.as_path(), Some("main"))
                .expect("Could not load program. Did you compile the sample programs? Run `make test` in the root directory.");
        let stripped_program = program.get_stripped_program().unwrap();
        let bootloader_version = 0;

        let program_hash = compute_program_hash_chain(&stripped_program, bootloader_version)
            .expect("Failed to compute program hash.");

        let program_hash_hex = format!("{:#x}", program_hash);

        assert_eq!(program_hash_hex, expected_program_hash);
    }
}
