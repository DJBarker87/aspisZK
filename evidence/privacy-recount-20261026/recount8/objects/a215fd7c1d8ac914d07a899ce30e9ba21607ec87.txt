# K-1-class finding: literal None reported as Some

**Classification (b): Kani reports a false failure.** K042's concrete counterexample passes optimized native Rust, including the observer assertion. A 17-line direct-call reduction reproduces the failure without any KMX registrations, function replacements, allocations, or copies. The defect belongs to the Kani/CBMC verification path, not to KMX. The internal compiler/backend pass responsible has not been localized. The current host reports CBMC 6.8.0; current compiler/backend binary hashes are retained in KNB_CLEANUP.json, without claiming historical executable identity.

## Configuration diff

The exact comparison is in [KNB_CONFIGURATION.md](KNB_CONFIGURATION.md), [KNB_config_hashes.json](KNB_config_hashes.json), the immutable historical snapshots, and the retained diffs.

- NBW_K026 receipt revision: `f84b1eed957b8d6d4e6c9176162a24f9ecd67549`; NBZ_K042: `14860f4d09e2daefcf2a8db3978f1d5b6adad3a3`. Both were dirty scratch builds. The positive target, its continuation and observer replacement are identical after prefix renaming. NBZ appends negative controls and imports NBZ_native/windows/steps. verifier.rs, lib.rs and KMX_stubs.rs are byte-identical.
- Both use Kani 0.67.0, `--lib -j 1 -Z unstable-options -Z stubbing --harness-timeout 90s --exact --output-format terse`, and `#[kani::unwind(4096)]`. Neither specifies a solver flag or solver attribute. The retained Kani help documents CaDiCaL as the default. Historical solver executable hashes were not captured, so exact historical binary identity cannot be claimed.
- Both apply six KMX replacements: ptr::copy_nonoverlapping, [u8]::copy_from_slice, [u8]::clone_from_slice, [u8]::to_vec, Vec<u8>::extend_from_slice, alloc::alloc::realloc. Both additionally replace verifier::mark with the respective prefix's mark_none. The mitigation patch is SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. The stub file is byte-identical to the retained mitigation file, SHA256 `ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138`.
- Both validate the frozen resolved graph from `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`: graph SHA256 `bb23b60cafd193e8149a16472d04d19832ef6aec4c9eac78c4e5827ff9fa9f48`; lock SHA256 `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`, unchanged afterward.
- Both use offline Cargo, one build job, dev optimization 3/debug 0, release overflow checks, and `RUSTFLAGS=-C link-arg=-Wl,--threads=1`. Scratch/target/TMPDIR paths differ by job prefix. The original receipts retain their absolute paths.

The diagnostic runs add `-Z concrete-playback --concrete-playback print --output-format regular` to obtain exact failures. These additions are recorded per receipt. K001 and K002 select the two prefix-equivalent harnesses in the same isolated source tree; K001 passes while the original NBZ selection fails. Renaming is not a repair or grounds to restore credit.

## Counterexample and native classification

K002 reproduces K042: **1/274 failed, 3/4 covers**, only `obs.is_none()` fails. Counterexample: `i=2, k=3, j=63`; [KNB_K042_playback.rs.txt](KNB_K042_playback.rs.txt) contains Kani's generated test. [KNB_counterexample.json](KNB_counterexample.json) retains all **533 primitive choices, 3176 bytes**.

Kani explicitly warns that native playback does not apply the original stubs. Accordingly [KNB_playback.rs](KNB_playback.rs) consumes the generated primitive bytes in order, uses the actual project carrier types, and explicitly calls the observer replacement from the literal continuation. It checks the assumptions, all original assertions, and consumption of every input. KNB_R001 runs this under `cargo test --release --locked --offline`: **one test passes**, including `obs.is_none()`, phase routing and call count. Thus the failure does not establish a shipped Rust defect or a harness observation of some other supplied callback. The source and replay both pass literal None.

## Cause isolation and reduced reproducer

K003 removes only the six KMX registrations from the original positive target: the same sole observer failure remains. Individual KMX toggles cannot be a necessary explanation once the failure occurs with every KMX replacement absent, so those runs were not spent.

K004 removes unrelated NBZ harnesses. K005 removes the carriers altogether and still fails `obs.is_none()` (1/58). K006 explicitly calls the replacement body and removes the mark replacement attribute: the same failure remains. K008 removes the now-unused declarations, leaving the 17-line source [KNB_MINIMAL.rs.txt](KNB_MINIMAL.rs.txt). K009 changes **only unwind 4096 to 64** and reproduces the failure. There are no loops on this active path.

The reduced source uses the actual `Observer = Option<fn(Phase)>` and Phase enum. A symbolic `i < 10` is stored in a global, then `check(None, Phase::Query(i))` asserts None, checks the phase payload against the global, and increments a call counter. Kani reports the None assertion false; the phase and counter checks do not fail. The one-value generated counterexample is retained in [KNB_minimal_playback.rs.txt](KNB_minimal_playback.rs.txt).

To replay exactly, install KNB_MINIMAL.rs.txt as `crates/aspis-r1-cost-probe/src/NBZ_native.rs` **in an isolated scratch copy**, retaining the module and function names and the frozen lock/graph. Select `verifier::candidate::NBZ_native::NBZ_return_carriers` with the K008 receipt command. K009's source differs only in the unwind attribute. This source has **no kani::stub attributes and no KMX includes**. The filename/names preserve the failing historical symbol context; no repository production source was edited.

K007 is a deliberately simpler KNB fixture, without the global phase/call-count checks, and passes at both bounds (10 checks each). It also changes helper/symbol context, so it does not prove that globals alone cause the defect. The established cause is a verification fidelity failure on the retained direct-call pattern; this work does not distinguish a Kani frontend/codegen bug from a downstream CBMC representation bug.

## Scope and handling

- Keep **NBW_K026 return-carrier credit OPEN**. NBZ_K042 fails its positive observer gate. NBZ_K007 fails that same observer assertion, so it is not a clean negative control for its intended false weight assertion.
- Review credits that rely on this `Option<fn(Phase)>`/phase/global-check observation pattern, preserving exact symbol/configuration context and requiring native counterexample inspection. Small passing fixtures do not certify the richer pattern.
- **No blanket KMX-credit withdrawal follows from this diagnosis.** KMX is absent from the reduced failing path. This finding does not establish a false PASS; it establishes a false FAIL. Do not infer either soundness or unsoundness of unrelated successful gates from it.
- Preserve the minimal case as a K-1-class tool-fidelity regression and report it upstream. Keep the affected credit quarantined until a tool fix or independently validated observation method is available. Neither a prefix rename, a smaller passing fixture, nor an explicit helper call is a validated repair.

## Receipts and resource/budget accounting

| Attempt | Configuration | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| KNB_K001 | K042 prefix renamed KNB, six KMX stubs | 0 | 80.240347 | 2765792 | 0 |
| KNB_K002 | Original NBZ, six KMX stubs | 1 | 72.182525 | 2757104 | 0 |
| KNB_K003 | Original NBZ, six KMX registrations removed | 1 | 65.569965 | 2757840 | 0 |
| KNB_K004 | Reduced carrier case, no KMX | 1 | 67.776050 | 2756784 | 0 |
| KNB_K005 | Observer only, mark replacement, no KMX | 1 | 6.820089 | 425936 | 0 |
| KNB_K006 | Observer only, explicit check call, no stubs | 1 | 6.776816 | 425484 | 0 |
| KNB_K007 | Simpler KNB direct case, bounds 4096 and 64 (two harnesses) | 0 | 6.591787 | 381580 | 0 |
| KNB_K008 | 17-line direct reproducer, bound 4096 | 1 | 8.756404 | 490344 | 0 |
| KNB_K009 | Identical direct reproducer, bound 64 | 1 | 7.797411 | 424840 | 0 |
| KNB_R001 | Exact original counterexample, native release, explicit observer check | 0 | 92.777840 | 552648 | 0 |

[KNB_RESULTS.json](KNB_RESULTS.json) and each attempt's receipt record exact target/command, source revision, source hashes, wall time, RSS, swap, limits and N/A axioms. Experimental receipt revisions are the worktree revision at launch, with dirty scratch inputs identified by hashes; the frozen dependency/source baseline remains 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Historical and diagnostic hashes are distinct fields, not interchangeable claims.

Every run has its own successful frozen-graph preflight and unchanged post-run lock hash. All scopes use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one scope at a time. Admission requires allowed=true and exit 0. Transport retries and own-input corrections are retained in KNB_NATIVE_TRANSPORT.jsonl and stage notes; no submitted solver was resubmitted.

Used **9 Kani command invocations / 10 harness verifications, 1 optimized Rust run, 0 Lean runs**. Stopped after the reduced direct failure and its matched bound check established the cause, per the diagnosis stop rule. No full manifest or unrelated regression was run. The owned persistent cache was seeded by copying the read-only query cache and is retained. KNB_CLEANUP.json records deletion of only this job's rebuildable outputs. No key material or retained shared cache was removed. No push.
