# Owner-approved client bundle — D516 continuation

**Source complete; release gate packet incomplete: new paired timing is blocked before launch.** Branch `codex/pv-c474-draft-20261029`, requested base `19c9611220205ef2aae2d6b435a874555e8f0ac5`. Production source freeze: `ba39168f67a4445ed60aac4aec2c6587cecc7336` (the exact revision is also recorded in `final-audit.json`). This completes the source for owner decisions 1, 6 and 7 on top of the accepted D474(C)/linux_raw first half. No merge, push, deployment or shipping repin is performed. The lead reviews and adopts the bundle after the remaining timing gate.

New client SHA-256: **`da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0`**, 2,281,512 bytes. This records a proposed replacement artifact, not a changed shipping pin.

## Gate results

| Gate | Result | Evidence |
|---|---|---|
| Locked/offline Rust 1.94.1 client build | PASS | `client-build.json`, N73501; final client built successfully before the audit-manifest error described below |
| Exact deployed client features | PASS: ct-host-prover ON; insecure-spend-fixture OFF | `client-cargo-tree-features.txt`, `client-unit-graph.json` (one root, devnet_spend), `client-resolved-features.json` |
| Default ELF fresh rebuild | PASS: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`, 1,563,728 bytes | N73504, `elf-default-affinity4/comparison.json` |
| Devnet ELF fresh rebuild | PASS: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`, 1,563,728 bytes | N73505, `elf-devnet/comparison.json` |
| Pool ELF fresh rebuild | PASS: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`, 605,704 bytes | N73506, `elf-pool/comparison.json` |
| Existing client unit tests | PASS: 3/3 | N73507 |
| Existing fixed-coin fixtures | PASS: transfer/withdrawal proof, public bytes, normalized result and physical ledger bytes equal verified controls | `fixed-fixture-comparison.json`, N73507 |
| Actual fixture-OFF client integration | PASS: four transfer/withdrawal runs accepted by default/devnet verifier ELFs with pinned Pool; settlement matches; duplicate reservation rejects without ledger change | `runtime-private/acceptance.json`, N73507 |
| Existing 1,000-pair differential | PASS: 1,000/1,000; 600 complete proofs, 100 rejected-prefix cases, four complete ordered oracle streams; physical ledgers audited | `corpus-6000/pipeline-final.json`, `corpus-ledger-audit.json`, N73508 |
| N7 signing/transport | PASS: exact Python invoke produces the same 158-byte signed transaction as current shipped client; short/extra records reject | `signing-fixture.json`, `shape-and-diagnostic-errors.json`, N73507 |
| CT private-input decoder | PASS, evidence class **instruction-trace comparison** | `ct-decoding.json`, `decoder-disassembly.txt`, N73507 |
| New combined-client paired timing | **BLOCKED BEFORE LAUNCH**, not measured | `timing-blocker.json` |
| Final source/artifact/key retention binding | Pending collection | N73511 / `final-audit.json` |

The prior D474 paired medians **−1.01% transfer and −0.70% withdrawal PASS under adopted D359(A)** for both the ratio and 15 s gate, labelled **measured under throttling, paired**. They are historical first-half evidence, not a new combined-client measurement. They are not UNDECIDED. `OPTIONAL-remove-timing.diff` is not applied; stdout timing remains, and the observer still sees external wall time.

### Timing blocker and exact remaining action

The shared `/home/dombarker/project-offloads/QUIET_WINDOW.json` still contains the earlier pv-c474 claim, expired at epoch `1793263180.3563738`; SHA-256 `7247d32316b1c4bfb61f0fc907ec521b5170738a2526df4998c6cb52159a2b0b`. The prescribed O_EXCL claim cannot create a new window while it remains. `pv-common.txt`, ruling (e), explicitly says **“Never delete or edit the marker.”** The marker was neither changed nor removed. Lead clearance (or an explicit user exception) was requested while the independent gates continued. Final preflight also observed one foreign capped job; that ordinary contention is separate from the immutable expired-file obstruction.

After the lead clears the expired marker, use `tools/pv-c474b-20261029/start-window.py` on the host when the existing quiet preflight passes, then run `bundle/timing.py` in N73509 using the existing capped wrapper with `PV_C474_QUIET_OWNER=1`. The prepared script executes the actual combined fixture-OFF client against the **current shipped control**, SHA-256 `30d883a8d97f12c315898aaf9170eb7a542b5e935881f089506fd4601ddb6a20`, never against the intermediate D474 draft. It alternates order over ten pairs per fixture, records thermal counters and external process duration, stops if a rolling median ratio exceeds 1.10, and requires final candidate median below 15 s. D359(A) uses the paired samples including throttled pairs. No universal unthrottled bound is claimed. New timing has consumed zero scopes; do not replay any successful gate to resume it.

## Exact client recipe

Run `tools/r1-cost-probe/build-client.sh`; its effective command is:

```sh
cd tools/r1-cost-probe
unset CARGO_ENCODED_RUSTFLAGS CARGO_PROFILE_CLIENT_PANIC RUSTC_BOOTSTRAP
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
cargo +1.94.1 build --profile client --locked --offline -j 4 \
  --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend
```

The `client` profile inherits release opt-level=3 and sets panic=abort. Compiler: rustc 1.94.1, commit `e408947bfd200af42db322daf0fadfe7e26d3bd1`, LLVM 21.1.8, x86_64-unknown-linux-gnu. No target-cpu override. Root workspace manifest, profiles, locks and release pins are unchanged. Unit-graph bootstrap is graph-only; production compilation unsets it. `client-build.json` records the exact script, compiler and artifact.

## Source changes and feature binding

`PATCH.diff` is the complete production bundle versus pre-D474 `a9a9781f8a`. `PATCH.incremental-from-19c9611220.diff` is only this continuation. Both reverse-apply checks pass against final source. No optional timing patch is included.

The top-level tool manifest directly enabled insecure fixtures. N73500 caught the second, transitive enabling edge in the host-prover dependency of `crates/aspis-r1-cost-probe/Cargo.toml`. Cargo features are additive, so changing only the top-level client manifest cannot disable it. Both source edges are removed; the workspace is untouched. A new explicit audit-only feature gates four fixture helpers (`tail_samples`, `prove`, `fixture_secret`, `prove_masked_fixture`) and the simulator module; fixture examples explicitly require it. **No simulator body, production prover/arithmetic body, or verifier body is edited.** The simulator is still available with the audit feature, with identical source and semantics. No simulator law is weakened.

Audit harnesses intentionally enable the two deterministic-constructor features; the actual client does not. All shared dependency profiles match; the only two feature differences are listed in `harness-parity.json`. `fixture-body-binding.json` checks that removing the four new cfg attributes restores the entire old prover file byte-for-byte. `fixture-feature-sites.json` lists every source test of the feature: these add fixture definitions/modules, with no cfg! branch or replacement production body. Successful fixture-OFF compilation proves the selected static production calls resolve without the added definitions. The finite fixture/differential checks therefore exercise identical production source bodies; they are **not whole-client machine-code equivalence**. V370 compiler preservation remains named.

The 1,000-pair gate freshly executes all combined-candidate cases 6000–6999. It reuses unchanged shipped controls read-only after verifying every public/proof/result/oracle file against the earlier committed manifest and comparison hashes. The unchanged full-file comparator checks all records and streams; both physical ledger trees are checked against the records. `baseline-corpus-reuse.json` and `corpus-pipeline-binaries.json` bind this reuse. No unchanged control proof generation is repeated.

## N7 port and decoder evidence

The prepared N7 patch SHA-256 is `66aa36518ada24bda6dc2727ee9df97d7ccb6913883855afbd922b60a61d7cc8`. Its Python hunk and named fixed-copy decoder are unchanged. `N7-port.diff` records the minimal Rust loader port: preserve D474's literal-only macro and map all fallible conversions, reads, open and keypair validation through `err`; one redundant comment is omitted. `N7-port.json` records provenance. The named candidate branch ref lacked these design/evidence files; their exact prepared bytes were already tracked at the requested HEAD and were added to this sparse checkout.

As the D283 inventory establishes, this client accepts public fixture selectors/snapshots and public transaction data; it constructs witness values internally. The externally supplied secret input is the signing seed in each retained keypair. Rust now receives exactly 64 raw bytes per public key count over an inherited pipe, then performs a named fixed copy. No decimal-key parser or fallback remains in Rust.

The actual optimized client executes the same nine decoder instructions for all-zero and all-0xff 64-byte records of equal public shape. PTRACE_SINGLESTEP compares relative PCs and input/output base-register offsets through RET, and checks both copies. Disassembly is eight fixed-offset MOVUPS loads/stores plus RET: no secret branch, early exit, length-dependent loop or table index. This is **instruction-trace comparison of the decoder slice**, not dudect, a same-public privacy experiment or whole-loader/signing CT. CPU latency V371, OS I/O and keypair consistency validation remain separate obligations.

The exact Python invoke function, extracted by AST to avoid top-level RPC, signs public RFC8032 vector 1 identically to the current shipped client: transaction SHA-256 `44e9ec48d04617ad3467573d95dc25d3797ab6581618959d11cd6eac23c8b41d`. Key file remains unchanged at mode 0600. Python decimal preparation, allocation, buffers, lifetime/storage, zeroization, scheduling and OS failures are not newly proved constant time by this Rust boundary repair. N7 is signing-seed custody, not witness privacy.

## Spans for pv-cx re-extraction

`changed-spans.json` pins each final file hash and exact spans against both bases. Final-source coordinates:

| File | Full bundle versus a9a9781f8a | Continuation versus 19c9611220 |
|---|---|---|
| `devnet_spend.rs` | 2–6, 14, 17–25, 27–39, 42–44, 49–53 | 14, 27–39, 49–53 |
| `devnet_spend/plan.rs` | 3; deletion at line-20 boundary; 29, 40, 108, 112, 114, 118, 123 | none |
| `devnet_spend/Client64_accounts.rs` | 2, 20 | none |

The full patch also supplies `diagnostics.rs`, build recipe/profile and the feature gates above. Historical extraction of a function name is not automatically rebound to this new client; pv-cx consumes these exact hashes/spans.

## Resources, failures and retained obligations

All scopes are sequential with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Rust work is optimized. `attempts.json` and per-scope receipts record exact target, exit, wall, maximum process RSS, swaps, source revision and `#print axioms` = N/A. No Lean or Kani ran. Native IDs N73500–N73508 and N73510–N73511 are used; N73509 remains reserved for new timing.

N73500 failed the feature preflight before compilation. N73501 built the final client, then its separate audit manifest failed because inherited default-run named an absent target; N73502 fixes that audit input and builds only the harnesses, without repeating the client build. N73503 failed before producing a default ELF because build-script LLVM linkers exhausted the task allowance; N73504 replaces it with four-core affinity under unchanged caps. Each failure and changed input is retained. Existing SBF stack-size diagnostics were emitted; final builds exited 0 and pins match. No cap was raised.

N73508 completed in 1:55:24; max process RSS 819,108 KiB, cgroup memory peak 6,444,740,608 B, zero swap, pids peak 54. Soft MemoryHigh reclaim events: 2,923; memory.max events 0, OOM/kill 0, pids-limit events 0. Ten-minute reviews retained the caps while cases continued to complete. Native fixture results do not become universal source-refinement or timing theorems.

Retain all task keys, recovery files and nonce ledgers. Runtime fixture keys are mode 0600 in a mode-0700 directory; the public RFC key is retained unchanged. No keys were deleted, no funds/authorities were cleaned up, and no transaction was broadcast. Build outputs/caches remain available for the blocked dependent timing gate in the assigned host directory.

No premise of `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` or T field is removed, added or weakened. The feature and raw-input deployment recipe is repaired in this proposed bundle; shipping adoption and new timing remain. E1/E2, V370/V371, whole-client L1/L2/L3, diagnostic/native I/O association, Python/storage and event-retaining RunJoin obligations remain. **Privacy target not yet established.** Next: lead clears the expired marker; finish the single new paired timing gate; pv-cx re-extracts the pinned spans and lead reviews/adopts.

The first N73510 barrier encountered a vanished foreign session cgroup (`FileNotFoundError`, session-468733.scope) before audit work started. Its refusal is preserved under `refusals/native73510-scan-race-01`; the same unlaunched ID is retried after the conservative full 180 s cooldown, under the documented transient-scan rule and unchanged caps. No proof, compile or timing run is resubmitted. Count the extra pre-work scope conservatively against the 40-scope ceiling.

N73510 then caught an inherited stale expected hash for `tools/pv-c474-validation/Cargo.toml`, an audit-only input changed by the already-recorded harness-manifest repair. `audit-manifest-correction.json` reconstructs the exact expected bytes from the generation recipe and checks literal host equality. N73511 repeats only the read-only binding audit with the corrected inventory. No production source, compiled harness or successful gate is changed or replayed.
