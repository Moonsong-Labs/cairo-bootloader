cargo run -- --program examples/starknet_with_keccak.json --layout starknet_with_keccak

cpu_air_prover --out_file proof.json --parameter_file proof/cpu_parameters.json --private_input_file proof/private_input.json --prover_config_file proof/prover_config.json --public_input_file proof/public_input.json 