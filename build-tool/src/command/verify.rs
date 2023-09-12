//! Verify the OS.

use std::result::Result as StdResult;

use anyhow::anyhow;
use clap::Parser;
use futures::future::join_all;
use serde::Deserialize;
use tokio::process::Command;

use super::{GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::Project;

#[derive(Deserialize)]
struct PackageMetadata {
    atmosphere: Option<AtmosphereMetadata>,
}

#[derive(Deserialize)]
struct AtmosphereMetadata {
    /// Whether to verify the crate.
    #[serde(default)]
    verified: bool,
}

/// Verify the OS.
#[derive(Debug, Parser)]
#[clap(trailing_var_arg = true)]
pub struct Opts {
    /// Extra arguments for Verus.
    extra_args: Vec<String>,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Verify);

    let project = Project::discover()?;

    let metadata = cargo_metadata::MetadataCommand::new()
        .current_dir(&project.root())
        .no_deps()
        .exec()?;

    let mut source_paths = vec![];
    for package in metadata.packages {
        let meta: Option<PackageMetadata> = serde_json::value::from_value(package.metadata)?;

        if let Some(meta) = meta {
            if let Some(atmosphere) = meta.atmosphere {
                if !atmosphere.verified {
                    continue;
                }

                let lib = package.targets
                    .iter()
                    .find(|target| target.kind == &["lib"] && target.crate_types == &["lib"])
                    .ok_or_else(|| anyhow!("Package {} must have a lib crate", package.name))?;

                source_paths.push(lib.src_path.as_std_path().to_owned());
            }
        }
    }

    log::debug!("{:?}", source_paths);
    log::info!("Verifying {} crates...", source_paths.len());

    let futures = source_paths
        .iter()
        .map(|root| {
            Command::new("rust_verify")
                .arg("--crate-type")
                .arg("lib")
                .arg(root)
                .args(&local.extra_args)
                .status()
        });

    join_all(futures).await
        .into_iter()
        .collect::<StdResult<Vec<_>, _>>()?;

    Ok(())
}
