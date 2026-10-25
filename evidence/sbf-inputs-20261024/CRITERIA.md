# SbfInputs criteria and design

Entry ed3227f4dae529ed61d7f63c9dbd5adb8028e953, assigned branch only.
Changes restricted to tools/sbf-inputs-20261024 and evidence/sbf-inputs-20261024.

1. Read merged SbfRecapturePrep and SbfCachePrep evidence via immutable Git.
   Reuse archive/source equality explicitly; never infer historical warm provenance.
2. Before host mutation verify resolved uid1000/0700/OWNER own stage and frozen
   manifest/lock/wrapper pins. Create only a new exclusive SbfInputs subdirectory.
3. Prepare exactly 123 public packages from retained checksum-matching .crate
   archives. Never traverse global unpacked sources or ICE logs. Preflight all
   member paths/types/modes/duplicates; stream ordinary files without tar extract.
   Reject links, specials, traversal, secret-shaped names and ambiguous packages.
   Preserve archives and published bytes/modes. Cargo-generated metadata requires
   selected official Cargo semantics; do not forge metadata or fingerprints.
4. Python-only preparation bounded by Linux RLIMIT_AS 512MiB; record exact
   invocation/revision/helper/runtime/input/output hashes, exit/wall/RSS/swap,
   axioms N/A. Preserve partial failures, no unchanged retry. Derived JSON >5MB
   remains remote with hash/size/path only. No packages installed/downloaded.
5. Commit literal helper and synthetic tests before any namespace probe.
   Assess existing isolation tools read-only; no privileged mounts/security changes.
   Exact old logical source/target/registry/tool paths must be preserved or their
   drift stated. Unknown feasibility remains an execution blocker.
6. Prepare three future commands: initial cold dependencies, default then devnet
   reuse fresh private cache, Pool separate logical target with only validated new
   dependencies. Historical snapshot is reference only. No old OUT_DIR reuse.
   Preserve wrapper bytes, -j4 and linker threads4; retain fixed ELF pins.
7. Future proposal only: sequential High3G/Max4G/Swap0/Tasks64, separately reviewed
   concurrency and prospective + actual GO inside exact scope; reservations <55GiB,
   OS/control reserve 7GiB. Cold peak unknown. Capture all descendant exec/file
   paths, not merely compiler-wrapper events; unknown input blocks release.
8. Zero builds, compiler queries, Cargo invocations, scopes, Lean/Kani/extraction/
   backend/ELF/consumer/full manifests, keys/RPC/chain. No theorem/premise/trust or
   shipped source changes. Both security targets and all release joins stay open.

Acceptance distinguishes prepared input facts, reused observations, proposals and
blocked execution. Smaller honest plan preferred to an unvalidated large sandbox.
