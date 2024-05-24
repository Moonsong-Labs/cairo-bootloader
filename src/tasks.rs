use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::program::Program;
use cairo_vm::vm::runners::cairo_pie::CairoPie;

use crate::{Task, TaskSpec};

#[derive(thiserror::Error, Debug)]
pub enum BootloaderTaskError {
    #[error("Failed to read program: {0}")]
    Program(#[from] ProgramError),

    #[error("Failed to read PIE: {0}")]
    Pie(#[from] std::io::Error),
}

pub fn make_bootloader_tasks(
    programs: &[&[u8]],
    pies: &[&[u8]],
) -> Result<Vec<TaskSpec>, BootloaderTaskError> {
    let program_tasks = programs.iter().map(|program_bytes| {
        let program = Program::from_bytes(program_bytes, Some("main"));
        program
            .map(|program| TaskSpec {
                task: Task::Program(program),
            })
            .map_err(BootloaderTaskError::Program)
    });

    let cairo_pie_tasks = pies.iter().map(|pie_bytes| {
        let pie = CairoPie::from_bytes(pie_bytes);
        pie.map(|pie| TaskSpec {
            task: Task::Pie(pie),
        })
        .map_err(BootloaderTaskError::Pie)
    });

    program_tasks.chain(cairo_pie_tasks).collect()
}
