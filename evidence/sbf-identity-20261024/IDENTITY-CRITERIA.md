# SBF identity criteria (committed before collection)

Scope: metadata only, immutable repository base 3e9998bbfc828c6e9455cc45a846dcd0f5372710;
frozen S10 source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. No build,
Lean, Kani, extraction, ELF execution, installation, chain action, or adoption.

Historical recovery requires a contemporaneous receipt binding the selected
compiler executable and its loaded libraries, target core/alloc archives, and
matching complete rust-src declaration tree to content hashes at S10 build time.
A path, crate filename, mangling, version, upstream commit declaration, or current
hash is insufficient. Retained official archive equality can identify current
contents, but does not retroactively prove historical selection.

Current collection must resolve and record symlinks before reading their targets;
stop any lookup entering another worker's private/live workspace. Read only global
installed toolchain/packaging metadata and named released snapshots. Do not read
keys or SDK program fixtures. Stream hashes; commit no binaries or large derived
JSON (over 5 MB: hash and size only). Version/sysroot queries are metadata, not
compilation. Record command, exit, wall, RSS, swap, revision, dependency hashes;
axioms are N/A for metadata.

If historical content identity is absent, the deliverable is an exact future P7
capture/reproduction plan, not a closure claim. Capture tool/source content before,
at go, and after all three independent capped builds; fail closed on drift or
ELF mismatch. New same-byte artifacts bind a new capture, not past sysroot identity.
Preserve unchanged proof evidence explicitly as reused. Do not hide execution or
output equivalence in a premise. No premise, security contract, or trust changes.

Expected ELF SHA-256:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

All proof/build gate budgets are zero in this job. Both deployed security targets
remain not yet established. Future builds require lead authorization, strict
finite populated reservations below 55 GiB and existing exclusive memory gates;
no proposed slab credit is adopted.
