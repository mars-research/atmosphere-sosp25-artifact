//! Runs GDB.

use std::process::ExitCode;

use clap::Parser;
use tokio::fs;

use super::{GlobalOpts, SubCommand};
use crate::emulator::GdbConnectionInfo;
use crate::error::Result;
use crate::project::Project;

/// Runs GDB.
#[derive(Debug, Parser)]
#[clap(trailing_var_arg = true)]
pub struct Opts {
    /// Pause at the very beginning.
    #[clap(long)]
    pause: bool,

    /// Extra arguments for GDB.
    extra_args: Vec<String>,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Gdb);

    let project = Project::discover()?;
    let json_path = project.gdb_info_path();

    if !json_path.exists() {
        log::error!("The GDB connection info file doesn't exist");
        log::error!("Hint: Try `atmo run --gdb` or `cargo run -- --gdb`");
        quit::with_code(ExitCode::FAILURE);
    }

    let json = fs::read(&json_path).await?;
    let gdb_info: GdbConnectionInfo = serde_json::from_slice(&json)?;

    gdb_info.launch_gdb(local.pause, local.extra_args).await?;

    Ok(())
}
