# K-2 follow-up: false failures and module-name-sensitive verdicts

**A — Over-approximation under the requested two-probe criterion:** both deliberately false properties fail explicitly. No false PASS was observed. This is a bounded diagnostic classification, not a proof that all Kani passes are sound.

**B — An otherwise identical program changes verdict when only its module identifier changes.** Original `NBZ_native` fails; `KNC_native` passes. Source declaration order and file placement are unchanged. **Passes cannot be assumed stable either.** The passing rename is a finding, never a repair or credit.

## A: exact-context false properties

The isolated source tree restores the captured KNB_K008 inputs byte-for-byte before the experimental edit; [setup receipt](KNC_SETUP-result.json) records the match. The file remains `crates/aspis-r1-cost-probe/src/NBZ_native.rs`, with original module, helper, globals, and harness names, and unwind 4096.

| Run | Sole experimental edit | Explicit result | Receipt and full output |
|---|---|---|---|
| KNC_K001 | `obs.is_none()` → `obs.is_some()` | `obs.is_some()` FAILURE; 1/58 checks fail | [receipt](KNC_K001/receipt.json), [log](KNC_K001/stdout.log) |
| KNC_K002 | payload `assert_eq!(i,NBZ_Q)` → `assert!(i >= 10)` | `i >= 10` FAILURE; original `obs.is_none()` also FAILURE; 2/49 fail | [receipt](KNC_K002/receipt.json), [log](KNC_K002/stdout.log) |

These are property-level failures, not conclusions inferred only from command exit. The observer argument is literally None. The harness assumes `i < 10` and passes that i as `Phase::Query(i)`, so the inverted payload assertion is false for every allowed input. Both negative probes therefore behave in the expected direction. The existing native replay remains in [KNB finding](../kani-diag2-20261028/KNB_FINDING.md); no new native claim is made here.

## B: name sensitivity isolated in two runs

| Run | Module | File / body / declaration order | Verdict | Receipt and full output |
|---|---|---|---|---|
| KNC_K003 | `KNC_native` | Original K008, unchanged | PASS, 0/58 fail | [receipt](KNC_K003/receipt.json), [log](KNC_K003/stdout.log) |
| KNC_K004 | `NBZ_native` restored | Same | FAIL, only `obs.is_none()`, 1/58 | [receipt](KNC_K004/receipt.json), [log](KNC_K004/stdout.log) |

The complete captured-source difference is exactly one identifier in candidate.rs:

```diff
-#[cfg(kani)] #[path="NBZ_native.rs"] mod NBZ_native;
+#[cfg(kani)] #[path="NBZ_native.rs"] mod KNC_native;
```

The command's selected fully qualified harness follows that identifier; every other switch, environment value, workspace/target/temp path, and captured source is identical between K003 and K004. NBZ_native.rs itself has the original K008 SHA256 `6cfbbb6bf6c4a16ed6a1963d3880790cb05b325925480e8476c14ae3ea24f8f3` in both. [Snapshot index](KNC_snapshot_index.json) links every captured input to its hash. The original-name restoration controls for this job's scratch paths and current environment rather than relying solely on the older K008 failure.

This establishes sensitivity to a module-name-only source change without source reordering. Whether that name changes internal codegen traversal/order, symbol representation, or another backend detail is not localized. No claim is made that internal codegen ordering is unchanged. Further function/helper/global renames are unnecessary once this comparison answers B, so they were not run.

## Existing-credit handling

Apply local-lean rule 14: quarantine (no credit, not withdrawn) every PASS whose property depends on an Option of a function pointer, a function-pointer value/comparison, or an observer held as Option<fn>. Preserve exact names/configuration and require an independently validated verification path or a validated tool correction before restoring credit. Neither this two-control direction result nor a passing rename clears the quarantine.

Known affected positive evidence in this follow-up chain:

- NBW_K026: `verifier::candidate::NBW_native::NBW_return_carriers`; keep return-carrier credit OPEN/quarantined.
- KNB_K001: `verifier::candidate::KNB_native::KNB_return_carriers`; PASS remains quarantined.
- KNC_K003: `verifier::candidate::KNC_native::NBZ_return_carriers`; diagnostic PASS only, quarantined and earns no credit.
- NBZ_K042 / KNB_K008 / KNC_K004 select `verifier::candidate::NBZ_native::NBZ_return_carriers` and fail; they cannot supply positive observer credit. NBZ_K007 is not a clean negative control because its positive observer gate already fails.

This is the known chain, not an exhaustive audit of all historical harnesses. Apply the same dependency-based quarantine to other credits during inventory. Do not withdraw all KMX credit: the minimal active path has no KMX registrations or stubs. No false PASS has been demonstrated here, but name-sensitive success prevents treating the observed false failures as a general stability guarantee.

## Configuration, resources, and stop

Frozen baseline: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen lock SHA256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Each Kani run has a preceding successful KNC_G00n metadata scope, exact resolved-graph comparison, and unchanged post-run lock hash in its KNC_K00n-graph-check.json. Offline Cargo, one build job, optimization level 3/debug 0, release overflow checks and original linker flags are preserved. Kani 0.67.0 / CBMC 6.8.0; current binary hashes are in [cleanup receipt](KNC_CLEANUP.json).

The command matches K008's flags: `--lib -j 1 -Z unstable-options -Z stubbing --harness-timeout 90s --exact`, the selected harness, `-Z concrete-playback --concrete-playback print --output-format regular`. Absolute workspace/target/temp paths identify this isolated job. Exact commands, worktree source revisions, source hashes, axioms N/A, limits, timings, RSS and swap are in each receipt.

| Run | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| KNC_K001 | 1 | 17.250 | 534292 | 0 |
| KNC_K002 | 1 | 7.740 | 424896 | 0 |
| KNC_K003 | 0 | 9.128 | 490408 | 0 |
| KNC_K004 | 1 | 9.195 | 490456 | 0 |

Used **4/10 Kani runs, including 2/4 name-comparison runs; 0/2 optimized Rust runs; 0 Lean**. Stopped when both questions were answered. All scopes ran sequentially with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Every admission had allowed:true and exit 0; no admission or transport retry was needed. No infrastructure was changed. No production crates/programs were edited.

Own persistent cache was seeded by COPYING the read-only query cache and retained; shared kmy cache was untouched. Only this job's rebuildable target/temp outputs were removed. Captured source snapshots, receipts and logs remain. No evidence file exceeds 20 MB. No keys were used or removed. No push.
