# Cairo bootloader

Cairo bootloader port for the Rust Cairo VM.

The Cairo bootloader is a Cairo program that loads and executes other programs in a provable way.
It is also able to execute Cairo PIEs (Position Independent Executables) along with regular Cairo programs.

We currently support Cairo bootloader v0.13.0.

## How to use this library

We provide two hint processors that can be used to execute bootloader hints.

### Standalone hint processor

The standalone hint processor (`BootloaderHintProcessor`) is the simplest way to execute the bootloader. 
You can just declare the hint processor and use it in `cairo_run_program`.

Check the [run program example](./examples/run_program.rs) for more details on how to configure the bootloader options.

### Minimal hint processor.

For advanced use cases, we also provide the `MinimalBootloaderHintProcessor` struct.
This is useful when you want to mix multiple hint processors (ex: Starknet OS hints + bootloader hints + builtin hints)
and avoid checking for the Cairo VM hints multiple times, or simply avoid compatibility issues between different
versions of `cairo-vm`.

To use this hint processor, you will need to define your own hint processor structure and implement the `HintProcessorLogic`
trait yourself.

Note that this is exactly how the `BootloaderHintProcessor` struct is implemented.

## Limitations

* Composite packed outputs are not supported yet.
* The bootloader is not able to load hints for Cairo 0 programs with hints yet.
