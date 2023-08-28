//! Verify the OS.

use std::path::PathBuf;
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
    /// List of modules to verify.
    ///
    /// Example: src/verified.rs
    #[serde(default)]
    verified_modules: Vec<PathBuf>,
}

/// Verify the OS.
#[derive(Debug, Parser)]
pub struct Opts {
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let _local = unwrap_command!(global, SubCommand::Verify);

    let project = Project::discover()?;

    let metadata = cargo_metadata::MetadataCommand::new()
        .current_dir(&project.root())
        .no_deps()
        .exec()?;

    let mut roots = vec![];
    for package in metadata.packages {
        let package_path = package.manifest_path.parent()
            .ok_or_else(|| anyhow!("manifest_path must have a parent"))?
            .as_std_path();

        let meta: Option<PackageMetadata> = serde_json::value::from_value(package.metadata)?;

        if let Some(meta) = meta {
            if let Some(atmosphere) = meta.atmosphere {
                let package_roots = atmosphere.verified_modules
                    .iter()
                    .map(|m| package_path.join(m));

                roots.extend(package_roots);
            }
        }
    }

    log::debug!("{:?}", roots);
    log::info!("Verifying {} modules...", roots.len());

    let futures = roots
        .iter()
        .map(|root| {
            Command::new("rust_verify")
                .arg("--crate-type")
                .arg("lib")
                .arg(root)
                .status()
        });

    join_all(futures).await
        .into_iter()
        .collect::<StdResult<Vec<_>, _>>()?;

    Ok(())
}
