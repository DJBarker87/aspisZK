# Shipped-file preservation and release gate

Base 73070ddd51; integrated source 420fbea022. `shipped-additions.json` records
both full-file hashes and exact candidate prefix length for every changed
crates/programs file. `tools/pv-dict2-20261027/shipped-check.py` verifies that
all pre-existing bytes are identical and parses every appended top-level item
as an explicitly `#[cfg(kani)]` module (15 modules across three files).
No production-code edits or deletion, and no programs/ change.

`crates/aspis-r1-cost-probe/src/lib.rs` exposes r1_wire without a feature gate
(line 13), and prover behind `#[cfg(feature = "prover")]` (lines 20–21).
`crates/aspis-prover/src/lib.rs` exposes state_only_hiding (line 23).
`programs/r1-cost-probe/Cargo.toml` selects optimized-terminal and program-build
on its aspis-r1-cost-probe dependency (line 22); thus r1_wire is shipped and its
crate location alone provides no exclusion. All additions carry cfg(kani),
which the SBF release commands do not enable. The other two files meet the
same stronger exclusion check regardless of release dependency reachability.

All three fresh capped optimized SBF builds match the requested pins:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Receipts in elf/ include exact commands, revision, resource limits, exit,
wall, peak RSS and swap. Axioms N/A for SBF. Time is in optimized compilation.
Three early metadata failures are retained: missing workspace input, missing
execute permission on copied diagnostic wrapper, missing transitive Cargo
path input. Each successor corrected its inputs; no failed build reran unchanged.

Build outputs remain on the owned host in candidate/build-*/artifacts; generated
keypairs retain mode 0600. No key was deleted, unlinked or copied into evidence.
