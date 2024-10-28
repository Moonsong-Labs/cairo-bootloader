use std::fs;
use std::{path::PathBuf, str::FromStr};
use std::error::Error;
use bootloader::{bootloaders::load_bootloader, tasks::make_bootloader_tasks};
use cairo_vm::types::layout_name::LayoutName;
use config::Template;
use runner::{cairo_run_bootloader_in_proof_mode, extract_execution_artifacts};

pub mod config;
pub mod runner;

use clap::Parser;

#[derive(Parser, Debug, Clone)]
#[clap(author, version, about, long_about = None)]
pub struct Args {
    #[arg(long, env)]
    pub program: String,
    #[arg(long, env)]
    pub layout: String,
}

fn main() -> Result<(), Box<dyn Error>> {
    let bootloader_program = load_bootloader()?;
    let args = Args::parse();
    let program_bytes = fs::read(args.program)?;
    let layout = LayoutNameWrapper::from_str(&args.layout)?.0;
    let tasks = make_bootloader_tasks(&[&program_bytes], &[])?;

    let mut runner = cairo_run_bootloader_in_proof_mode(&bootloader_program, tasks,layout)?;

    let mut output_buffer = "Program Output:\n".to_string();

    runner.vm.write_output(&mut output_buffer)?;
    extract_execution_artifacts(runner)?;
    
    Template::generate_from_public_input_file(&PathBuf::from_str("proof/public_input.json").unwrap(), None,None).save_to_file(&PathBuf::from_str("proof/cpu_parameters.json").unwrap());
    Ok(())
}
pub struct LayoutNameWrapper(pub LayoutName);


impl FromStr for LayoutNameWrapper {
    type Err = String;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        let layout_name = match input {
            "plain" => LayoutName::plain,
            "small" => LayoutName::small,
            "dex" => LayoutName::dex,
            "recursive" => LayoutName::recursive,
            "starknet" => LayoutName::starknet,
            "starknet_with_keccak" => LayoutName::starknet_with_keccak,
            "recursive_large_output" => LayoutName::recursive_large_output,
            "recursive_with_poseidon" => LayoutName::recursive_with_poseidon,
            "all_solidity" => LayoutName::all_solidity,
            "all_cairo" => LayoutName::all_cairo,
            "dynamic" => LayoutName::dynamic,
            _ => return Err(format!("Invalid layout name: {}", input)),
        };
        Ok(LayoutNameWrapper(layout_name))
    }
}