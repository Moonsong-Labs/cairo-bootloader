# Cairo bootloader

Cairo bootloader port for the Rust Cairo VM.

The Cairo bootloader is a Cairo program that loads and executes other programs in a provable way.
It is also able to execute Cairo PIEs (Position Independent Executables) along with regular Cairo programs.

## How to use this library

Add this library to your dependencies, then launch your programs this way:

```rust
use cairo_bootloader::BootloaderHintProcessor;
use cairo_vm::types::program::Program;

fn run_program_with_bootloader(bootloader_program: &Program, program: &Program) -> Result<(), HintError> {
        let proof_mode = true;
        let layout = layout.unwrap_or(Layout::StarknetWithKeccak);
    
        let cairo_run_config = CairoRunConfig {
            entrypoint: "main",
            trace_enabled: true,
            relocate_mem: true,
            layout: &layout.to_string(),
            proof_mode,
            secure_run: None,
            disable_trace_padding: false,
            allow_missing_builtins,
        };
    
        let n_tasks = tasks.len();
    
        let bootloader_input = BootloaderInput {
            simple_bootloader_input: SimpleBootloaderInput {
                fact_topologies_path,
                single_page: false,
                tasks,
            },
            bootloader_config: BootloaderConfig {
                simple_bootloader_program_hash: Felt252::from(0),
                supported_cairo_verifier_program_hashes: vec![],
            },
            packed_outputs: vec![PackedOutput::Plain(vec![]); n_tasks],
        };
}
```

## Limitations

* Composite packed outputs are not supported yet.
* The bootloader is not able to load hints for Cairo 0 programs with hints yet.
