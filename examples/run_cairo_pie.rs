use std::error::Error;

use cairo_bootloader::cairo_run_bootloader_in_proof_mode;
use cairo_bootloader::tasks::make_bootloader_tasks;

fn main() -> Result<(), Box<dyn Error>> {
    let fibonacci_pie = include_bytes!(
        "../dependencies/test-programs/bootloader/pies/fibonacci-stone-e2e/cairo_pie.zip"
    );

    let tasks = make_bootloader_tasks(&[], &[fibonacci_pie])?;

    let mut runner = cairo_run_bootloader_in_proof_mode(tasks)?;

    let mut output_buffer = "Bootloader output:\n".to_string();
    runner.vm.write_output(&mut output_buffer)?;
    print!("{output_buffer}");

    Ok(())
}
