mod build;

use crate::build::build;
use clap::{Parser, Subcommand};
use std::path::Path;

fn main() {
    match Cli::parse().command {
        Command::Build { file } => build(&file),
        Command::Server => todo!(),
    }
}

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Build a program
    Build {
        /// Path to a source file
        file: Box<Path>,
    },
    /// Start the language server
    Server,
}
