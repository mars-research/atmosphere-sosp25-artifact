//! Command-line interface.

macro_rules! unwrap_command {
    ($global:expr, $type:path) => {
        if let $type(local) = $global.cmd {
            local
        } else {
            panic!("Invalid command {:?}", $global.cmd)
        }
    };
}

//mod build;
mod gdb;
mod run;
mod verify;

use clap::{CommandFactory, Parser};
use clap_complete::Shell;

/// Run the CLI.
pub async fn run() -> Result<(), anyhow::Error> {
    let opts = GlobalOpts::parse();

    match &opts.cmd {
        SubCommand::Run(_) => run::run(opts).await?,
        //SubCommand::Build(_) => build::run(opts).await?,
        SubCommand::Gdb(_) => gdb::run(opts).await?,
        SubCommand::Verify(_) => verify::run(opts).await?,
        SubCommand::GenCompletions(local) => {
            gen_completions(local.shell);
        }
    }

    Ok(())
}

/// Atmosphere build utility.
#[derive(Debug, Parser)]
struct GlobalOpts {
    #[clap(subcommand)]
    cmd: SubCommand,

    /// Use verbose output.
    #[clap(short, long, global = true)]
    verbose: bool,

    /// Build in release mode.
    #[clap(long, global = true)]
    release: bool,
}

#[derive(Debug, Parser)]
enum SubCommand {
    Run(run::Opts),
    //Build(build::Opts),
    Gdb(gdb::Opts),
    Verify(verify::Opts),

    #[clap(hide = true)]
    GenCompletions(GenCompletions),
}

#[derive(Debug, Parser)]
struct GenCompletions {
    #[clap(index = 1)]
    shell: Shell,
}

fn gen_completions(shell: Shell) {
    clap_complete::generate(
        shell,
        &mut GlobalOpts::command(),
        "atmo",
        &mut std::io::stdout(),
    )
}
