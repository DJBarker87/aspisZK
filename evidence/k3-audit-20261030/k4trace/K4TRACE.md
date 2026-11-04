# D645: retained matched-control execution traces

Branch `codex/pv-k4trace-20261104`, base `670416be996ba5a0e1c5fb6349a7db34f16714d0`; worktree `/Users/dominic/ZK/.worktrees/pv-k3scan`. Receipts are confined to this directory. No implementation, harness, assertion, bound, cap, recount or ledger edits; 0 Lean and `#print axioms` N/A. No push.

These are recommendations for Recount 13, restricted to each original qualified credit. All source files and six executable hashes are checked against retained pins before each launch. Exact historical C084 and projection source snapshots are replayed privately because the current host copies have since changed; preflight.json discloses those differences. Recovery changes no source bytes. Source packages and provenance are retained in source-payload.json.xz, source-provenance.json and retained-k3-sources.json.xz. Original commands/receipts are under original/.

Pinned Kani 0.67.0, bundled rustc 1.93.0-nightly (53732d5e0), CBMC 6.8.0 and kissat 4.0.1 match original/tools.json by SHA-256. K93109–K93111 original receipts record the harness revision/command but no per-run executable hashes; the standing globally pinned installation is checked against the retained Kani/CBMC executable pins rather than inventing historical per-run hashes. No toolchain is installed or changed. Existing std-transfer and compiler-cohort qualifications remain.

Every run uses one scope at a time, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, CPU0–3, original solver/timeout/features and original optimized profile. C084 preserves its original dev-profile defaults (opt-level=3); the other packages explicitly disable debug assertions and overflow checks. Both admission checks require allowed:true and exit0; quiet-marker snapshots and 180-second spacing are retained. Wall/RSS columns list the scopes in the displayed order. Peak RSS is GNU time's maximum process RSS in KiB; the receipt also retains aggregate cgroup memory peak bytes. Swap is both GNU time and cgroup swap peak.

| Credit | Harness/filter | Source SHA-256 (complete primary file) | Kani | Scope IDs | Wall seconds | Peak RSS KiB | Swap | Positive verdict | Control verdict | Trace location | Classification |
|---|---|---|---|---|---|---|---|---|---|---|---|
| C044 | path_checks::pathbuf_borrows | e2e80df1364f5c614b9880d76506e32f622d5e6dd6cffdd5c1a6594352b41a15 | 0.67.0 | K93512 / K93502 | 1.309 / 1.392 | 72004 / 175896 | 0 | SUCCESSFUL; exit 0; 0 of 352 checks failed | FAILED; intended path_checks::pathbuf_borrows.assertion.1 | lib.rs:74:44 | RESTORE |
| C084 | split_checks::string_path / split_checks::string_path_negative | 64f58eb51dbecb0dae785132a806593a6ce1fc9d8651ea3ec499e016f18a4b92 | 0.67.0 | K93503 / K93504 | 3.823 / 3.149 | 246600 / 246484 | 0 | SUCCESSFUL; exit 0; 0 of 524 checks failed | FAILED; intended split_checks::string_path_negative.assertion.2 | lib.rs:145:13 | RESTORE |
| C088 | sealed::pv_alib_checks::split64_coordinate_lo | 41b348246dbcfb2b7d580cbc1fc048641b311e821a6ca89b3137040b9f78f2c4 | 0.67.0 | K93505 / K93506 | 57.578 / 61.533 | 3072096 / 3126772 | 0 | SUCCESSFUL; exit 0; 0 of 426 checks failed | FAILED; intended inverted block-length assertion via assert_failed_inner | src/sealed.rs:105 → core/panicking.rs:439 | RESTORE |
| C089 | sealed::pv_alib_checks::split64_coordinate_hi | 41b348246dbcfb2b7d580cbc1fc048641b311e821a6ca89b3137040b9f78f2c4 | 0.67.0 | K93507 / K93508 | 69.153 / 63.446 | 3071744 / 3126844 | 0 | SUCCESSFUL; exit 0; 0 of 426 checks failed | FAILED; intended inverted block-length assertion via assert_failed_inner | src/sealed.rs:123 → core/panicking.rs:439 | RESTORE |
| K93109 | indexed_m31 | 073fd146dc0eab518888d55f24bda3623e1abbad8d2ebcbc345af05fc91b6e49 | 0.67.0 | K93513 | 9.373 | 533928 | 0 | SUCCESSFUL; original positive passes (1 pass / 2 intended controls fail) | Both original controls FAIL at intended assertions (value XOR1 / frame XOR1) | src/indexed.rs:42 and :44 | RESTORE |
| K93110 | indexed_qm31 | 073fd146dc0eab518888d55f24bda3623e1abbad8d2ebcbc345af05fc91b6e49 | 0.67.0 | K93510 | 5.770 | 183740 | 0 | SUCCESSFUL; original positive passes (1 pass / 2 intended controls fail) | Both original controls FAIL at intended assertions (value XOR1 / frame XOR1) | src/indexed.rs:42 and :44 | RESTORE |
| K93111 | indexed_wide | 073fd146dc0eab518888d55f24bda3623e1abbad8d2ebcbc345af05fc91b6e49 | 0.67.0 | K93511 | 5.053 | 183836 | 0 | SUCCESSFUL; original positive passes (1 pass / 2 intended controls fail) | Both original controls FAIL at intended assertions (value XOR1 / frame XOR1) | src/indexed.rs:42 and :44 | RESTORE |

Full scope IDs are `pv-k4trace-<ID>`. For each scope, `scope-command.json`, `STARTED.json`, `identity.json`, `metadata.json`, `receipt.json`, `time.log`, `cbmc-*-command.json`, full raw `cbmc-*.json[.xz]`, and `symbols-index.json` retain the exact execution and symbol mapping. The positive C044 cached goto symbol dump was recovered read-only inside its control scope K93502, explicitly indexed by the K93512 command receipt. K93500 and K93501 are disclosed in OUTPUT-MODE.md; metadata-only K93509 is disclosed in SETUP-K93509.md and its exact workspace recovery in workspace-recovery.json; neither is substituted for a green positive. K93501's apparent failure is fully classified as raw reachability-probe reporting, with no failing program property. The transparent tee forwards the unchanged CBMC stdout to the unchanged pinned driver, preserving normal Kani verdict processing.

## C044

The full control trace assigns n=0, i=0, len=0 and r.len=0. The intentionally inverted assert_ne!(len,r.len()) fails on equal zero lengths. Checked get queries return None on the empty slice; no wrapped pointer offset supplies this failure. Full trace and numbered excerpts: host/K93502/trace-excerpt.json.

## C084

Original control has literal [65;2] and i=0. Full trace has Path and String length 2, both get(0) replies pointing to dynamic_object, and compares byte 65 with byte 65 (trace steps 1216-1218). Option<&u8>::ne returns FALSE (1229), failing the intended inverted assertion at 145. No full-width offset truncation causes this failure. Full trace and numbered excerpts: host/K93504/trace-excerpt.json.

## C088

Control feature negative-lo activates assert_ne!(blocks.len()*64,rb.len()) at sealed.rs:105. The full trace sets n=0 and the compared scalar lengths to 0 and 0 (steps 509-525), then calls assert_failed::<usize,usize> and reaches assert_failed_inner at panicking.rs:439. This is the intended false scalar inequality; the large unconstrained b/j values are not dereferenced before that assertion. No 48-bit offset alias supplies the failure. The prior panic-placeholder summary is now resolved to its caller and operands. Full trace and numbered excerpts: host/K93506/trace-excerpt.json.

## C089

Control feature negative-hi activates assert_ne!(blocks.len()*64,rb.len()) at sealed.rs:123. The full trace assigns n=65, blocks.len()=1 and compared lengths 64 and 64 (steps 19612-19628), then calls assert_failed::<usize,usize> and reaches panicking.rs:439. It therefore fails the intended scalar inequality. No wrap of an unconstrained pointer offset is needed; the later coordinate dereferences are not reached before this assertion. Full trace and numbered excerpts: host/K93508/trace-excerpt.json.

## K93109

The positive passes and both controls fail only their intended non-probe assertions. Value failure is result[lane] versus bits[lane]^1 at line 42; frame failure is framed[lane] versus expected^1 at line 44. Full raw traces and numbered terminal assignments are retained in control-assessment.json and trace-excerpt.json. Logical offsets stay in u128; physical destination offsets are only 0 or 1 in the frozen two-place projection. Thus these failures are the deliberate XOR mutations, not 48-bit aliasing. Recorded control states: line 44: index=576460752303423488ul, query=0ul, byte_index=2305843009213693952; line 42: index=576460752303423488ul, query=0ul, byte_index=2305843009213693952. Full trace and numbered excerpts: host/K93513/control-assessment.json.

## K93110

The positive passes and both controls fail only their intended non-probe assertions. Value failure is result[lane] versus bits[lane]^1 at line 42; frame failure is framed[lane] versus expected^1 at line 44. Full raw traces and numbered terminal assignments are retained in control-assessment.json and trace-excerpt.json. Logical offsets stay in u128; physical destination offsets are only 0 or 1 in the frozen two-place projection. Thus these failures are the deliberate XOR mutations, not 48-bit aliasing. Recorded control states: line 44: index=144115188075855872ul, query=0ul, byte_index=2305843009213693952; line 42: index=144115188075855872ul, query=0ul, byte_index=2305843009213693952. Full trace and numbered excerpts: host/K93510/control-assessment.json.

## K93111

The positive passes and both controls fail only their intended non-probe assertions. Value failure is result[lane] versus bits[lane]^1 at line 42; frame failure is framed[lane] versus expected^1 at line 44. Full raw traces and numbered terminal assignments are retained in control-assessment.json and trace-excerpt.json. Logical offsets stay in u128; physical destination offsets are only 0 or 1 in the frozen two-place projection. Thus these failures are the deliberate XOR mutations, not 48-bit aliasing. Recorded control states: line 44: index=72057594037927936ul, query=0ul, byte_index=2305843009213693952; line 42: index=72057594037927936ul, query=0ul, byte_index=2305843009213693952. Full trace and numbered excerpts: host/K93511/control-assessment.json.

## Consequences and retained obligations

May restore the pre-Recount-12 CLOSED-ON-CANDIDATE bounded PathBuf scopes; no new deployed std/native or whole privacy claim. Lead applies this at Recount 13.

C084 does not supply V179's current independent structural support. C088/C089 do not replace C002 or discharge V233's independent typed/native association. K93109–K93111 cover only the segregated logical-offset/two-place projection; the original ptr.add/allocation/OWNER association remains OPEN. Every historical K-1/K-2/K-3, copy-stub, std parity/structural k''', feature, compiler V370 and world qualification is retained. No new T field or endpoint premise is introduced.

Before/after endpoint statements are unchanged: PrivacyR1HeadlineDeployedReal.privacy_headline_deployed loses no premise and gains no premise. E1/E2, actual RunJoin, proof-account client, L1/L2/L3, coherent dependency replay and axioms obligations remain. Privacy target not established. The next action is for the lead to feed these per-credit decisions into Recount 13; this job does not edit those authoritative files.

## Final receipt check

validation.json is PASS: eleven credited replay scopes (seven positives and ten matched controls across seventeen harness executions), exact source/tool pins, retained non-probe failure traces and symbol hashes, compliant admissions/caps, no swap and minimum credited launch gap 180.431 seconds. Total credited scope wall time 281.578 seconds; maximum GNU-time peak RSS 3126844 KiB. Three extra diagnostic scopes K93500/K93501/K93509 remain disclosed; the metadata-only K93509 has explicitly unavailable wall/RSS/swap usage metrics. No program-positive assertion failure was found. Archive hashes pass and no committed artifact exceeds 20 MiB. cleanup.json records no remaining live task scope and removal of only this job's target/tmp caches after retention.
