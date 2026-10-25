# Primary Cargo source assessment before execution

Primary revision ca74c32f0ac6d99000858dcae9b0931ef76a8f43, official
rust-lang/cargo raw files sealed in SbfResolve-research.json. Retained source text
is research data, not a dependency installation. CLI metadata.rs exec constructs
OutputMetadataOptions then calls output_metadata, printing JSON. No build dispatch.

cargo_output_metadata.rs27-67: no_deps serializes ws.members directly, resolve=None.
Full path152-220 builds RustcTargetData, Packages::All (whole workspace),
HasDevUnits::Yes, force_all_targets No with filter-platform, then resolve_ws_with_opts.
It serializes packages and graph, never invokes BuildRunner/compile/custom_build.
resolve.rs138-272 resolves registry/lock/features and download_accessible;
package.rs451-570 recursively collects accessible package IDs and get_many downloads
and loads package metadata. It does not compile/execute any package source. The
custom_build/proc-macro target fields are serialized data, not execution requests.
This is distinct from the build-runner direct build-script execution counterexample
already documented in SbfCachePrep, which is retained and not solved by a wrapper.

context/mod.rs423-450 loads Rustc::new; rustc.rs60-68 queries exact -vV.
target_info.rs174-220 queries empty stdin '-' --crate-name ___ --print=file-names,
optional --target sbpf-solana-solana, six --crate-type values bin,rlib,dylib,cdylib,
staticlib,proc-macro, --print=sysroot --print=split-debuginfo --print=crate-name
--print=cfg -Wwarnings. These are print-only discovery calls; proc-macro here is
an output-filename query, not loading a proc macro. No emit/output/codegen flags.
Unstable target-spec query requires build_std, absent here; guard denies it.
Unknown or changed argv safely denies, including every response file and real
source filename. Wrapper verifies selected rustc bytes and refuses nonempty stdin.
No compiler query ran during guard tests. Source route exclusion, not wrapper,
is the reason build-script execution is excluded for these metadata commands.

context/mod.rs1679-1706 discovers .cargo/config or config.toml at cwd and ancestors,
then CARGO_HOME. Extensionless wins. Manifest directory is not a config-search
root merely because --manifest-path names it. Clean ordinary /tmp own cwd will
have both config names absence-checked at each ancestor; only new private
CARGO_HOME/config.toml is supplied, offline=true. No actual user config/credentials
will be read to fill gaps. Explicit env excludes rustup proxies, auto-install,
build flags, external credentials and wrappers; RUSTC and selected Cargo are exact
absolute official platform paths. HOME/RUSTUP_HOME/CARGO_HOME/TMPDIR/target-dir are
new own paths. Source .cargo/config.toml is separately pinned, not loaded.

Scope: default features, no all-features/no-default-features override. Full query
uses sbpf-solana-solana filter; workspace/dev/host metadata scope is wider than
r1-cost-probe compiled dependencies. Even success proves neither exact future
compiled units nor future original-S10 environment equality.
