# Integrated source gates

Base: `0c9dc9a4cc`. Integrated merge revision: `5465d05960f6433ec1b465037f36829cb58dec8f`.

The only changed crates/programs file is `crates/aspis-r1-cost-probe/src/host_commitment.rs`. Its entire appended diff consists of three modules gated by `#[cfg(kani)]`: `pv_cblib_library_checks`, `pv_cblib_resume_checks`, and `pv_cblib_array_reject_checks`. The production prefix is byte-identical; see `crates.diff`. No programs/ or scripts/ changes.

The complete tools/ inventory is `changed-files.txt`. These are standalone extraction/reference/proof/evidence tooling, not cfg(kani) modules. A literal assertion that every tools/ file is inside cfg(kani) would be false. They are outside the release workspace members and are not selected by the three release manifests; none modifies a release build script. Cargo workspace member/feature manifests are unchanged by these merges. Ruling (l)'s relevant release-source condition is satisfied by the three cfg(kani) modules; ELF equality remains a separate mandatory gate.

The crate's host_commitment module is feature-gated in lib.rs, but that alone is not used as the gate: the added modules themselves have cfg(kani), which the release build does not enable.

Exact parent gate: `crates/aspis-r1-cost-probe/src/lib.rs:34` is `#[cfg(feature="prover")] mod host_commitment;`. `programs/r1-cost-probe/Cargo.toml` selects `optimized-terminal, program-build` and the pinned build adds `pool-adapter, private-leaf-salts`; none selects prover or cfg(kani). The other release manifests do not select this module. `source-gate-check.json` records prefix identity and all three appended gates.
