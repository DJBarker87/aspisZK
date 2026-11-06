# NKX legacy Pool removal handoff

Completed engineering gates; awaiting lead review/adoption. Branch:
`codex/cx-legacy-removal-20261107`. Source/artifact revision:
`3c53b641aff` (full hash in NKX_ELF.json); frozen comparison:
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.

Removed dispatch and exclusive source for ASIN/ASDI/ASPT/ASWD/ASPP/ASPF/ASPX.
All now fall through to InvalidInstructionData. Deleted: 8 files and 289
functions (including 54 tests); one rejection test added. Every deleted
function/test has a frozen file:line and restore command in NKX_REMOVED.md;
NKX_DIFF.patch is the complete Pool diff. Shared AS8I/AS8D and ASJP/ASJW
codecs remain exactly frozen even when their names/magic constants are legacy.

Byte identity: 427 direct frozen body/full-function checks pass, with matching
NKS hashes wherever that inventory has a row. Every retained pair*.rs file is
byte-identical. Only process_instruction differs among surviving functions:
exactly the seven removed branches. Six demonstrably spurious conservative
inventory targets (seven induced rows) are resolved by source/type inspection;
all incoming edges and reasons remain in NKX_BYTE_IDENTITY.json. Root/source
supplement includes AS8I codecs omitted from the emitted inventory. No genuine
pair-forest body differs. crates/, programs/r1-cost-probe/ and Cargo.lock have
empty diffs from frozen source; all host compiler-input hashes match the
frozen/final source manifests. No other program or proof source was edited.

Tests: frozen deployed baseline 118 unit + 2 ABI tests pass. Final deployed
67/67, default 36/36, disabled-route configuration 67/67, audit-feature union
72/72. The last suite executes ALL 72 remaining test names, including native
pair-forest account/state/CPI integration tests (NKX_TEST_COVERAGE.json).
All 54 removed tests are listed in NKX_TESTS.md and NKX_REMOVED.md.

Artifacts (native Linux ELa recipe, unchanged pinned tools/deployed features):
- Pool: `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc`,
  345648 bytes, reproduced twice; second build performs fresh Pool codegen.
- Default verifier: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`, unchanged.
- Devnet verifier: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`, unchanged.

NKX_ELF.json and per-mode receipts record exact commands/features, source
revision and source-manifest hashes, tool pins, resolved packages/features,
lock before/after, exit, wall, peak RSS, cgroup peak and swap. All final build
and test exits are zero; all swaps zero. #print axioms: N/A (no new theorem).
No cryptographic/security premise was discharged, added or changed. This is
source/artifact engineering evidence, not a 100-bit security conclusion.

Budget: 11/12 build/test scopes, 0 Kani, 0 Lean, 0 extraction. One scope at a
time, 6G high/8G max/Swap0/Tasks64, 600-second timeout, optimized Rust, -j4.
Every scope has allowed=true/exit0 admission and an inside-scope barrier.
No timeout, OOM, cap increase or unchanged failed-shape retry. Two compile
failures retained: task/thread spawning (own runner fixed by affinity 0–3),
and missing shared AS8I codecs (restored exact frozen source, then passed).
The static audit's overloaded From key association was repaired and its
inventory/direct-hash assertions strengthened. Original failures are retained.

Procedural deviations: a baseline admission retry occurred at about 65 s
instead of 180 s (no launch); a tests-deployed retry at about 136 s launched
only after allowed=true/exit0 plus the inside-scope barrier. Neither bypassed
a refusal. The later tests-all retry waited over 180 s. Original admission
logs and refusals remain in NKX_admission and NKX_ATTEMPTS.jsonl.

Host: /home/dombarker/project-offloads/codex-cx-legacy-removal-20261109.
Every scope checked at least 40 GB free; final free space is recorded in
NKX_CLEANUP.json. Largest observed own tree: 1,168,732,862 bytes, below 20 GB.
Only own Cargo target was removed after all builds; sources, ELFs, diagnostics
and receipts remain. No forbidden cache or other live worktree was touched.
No key files were created/read/deleted, wallets/funds accessed, push or
on-chain deployment performed. Non-key directory placeholders suppress the
build tool's key generation; the pinned [Agave post-processing source](https://raw.githubusercontent.com/anza-xyz/agave/v3.1.13/platform-tools-sdk/cargo-build-sbf/src/post_processing.rs)
checks path existence before creating a key. Cleanup verifies zero key files.

Remaining: lead reviews this candidate, records the adopted Pool source/ELF
pin in the security contract, and regenerates the post-removal Pool inventory
outside this job's authorized write scope. All requested engineering gates
are complete; no remaining member needs a twelfth build/test scope. The
100-bit per-attempt target, privacy and two-transaction design are unchanged;
the overall release target remains not established.
