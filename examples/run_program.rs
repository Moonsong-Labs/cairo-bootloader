use std::error::Error;

use cairo_bootloader::bootloaders::load_bootloader;
use cairo_bootloader::cairo_run_bootloader_in_proof_mode;
use cairo_bootloader::tasks::make_bootloader_tasks;

fn main() -> Result<(), Box<dyn Error>> {
    let bootloader_program = load_bootloader()?;
    let fibonacci_program = include_bytes!("fibonacci.json");

    let tasks = make_bootloader_tasks(&[fibonacci_program], &[])?;

    let mut runner = cairo_run_bootloader_in_proof_mode(&bootloader_program, tasks)?;

    let mut output_buffer = "Bootloader output:\n".to_string();
    runner.vm.write_output(&mut output_buffer)?;
    print!("{output_buffer}");

    Ok(())
}
