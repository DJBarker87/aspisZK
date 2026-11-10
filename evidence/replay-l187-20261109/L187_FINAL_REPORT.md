# L187 final report: cold replay of the TAS_FinalB closure

Date: 2026-11-10. Worktree branch codex/cx-integrate-20261107. Replay source revision at the end of the
replay: 4f98f106449 plus this report's commit. Host workspace:
/home/dombarker/project-offloads/codex-cx-replay-l187-20261109.

## 1. Scope and toolchain

The closure is the import closure of TAS_FinalB. It has 14,101 project modules and 19,862 loaded objects
in total, counting base libraries. Every object header in the closure records Lean v4.32.0. Every replay
compile used the pinned sysroot /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0 with
`lean -j1 -M7000 -DElab.async=false` and a 180 s timeout per module.

LEAN_PATH for every replay compile and audit step was `objs/` (replayed objects only), then `base_ref/`
(symlinks to the unchanged Mathlib/Aeneas/Aesop/Batteries/CompPoly base). The final steps also put
`final/objs/` first. No project module resolves from base_ref (checked: 0 of 14,101). No overlay object was
on any LEAN_PATH.

## 2. Outcome of every replayed object

Every one of the 14,101 modules was rebuilt (driver ALERT_END: PASS_IDENTICAL 10,815, PASS_DIFFERS 3,286;
0 pending, 0 failed, 0 skipped). L187_Compare was then run once more over every byte-differing object,
forward (overlay to replay) and reverse (replay to overlay), in one capped scope (final/L187_compare_all.py;
12.8 s, 516,904 KiB, swap 0; 0 tool errors). Results are in final/L187_COMPARE_ALL.jsonl.xz and
final/L187_CONSOLIDATED.json.

| Outcome | Modules |
|---|---|
| byte-identical to the overlay object | 10,815 |
| declaration-identical (bytes differ only in the embedded source path) | 3,245 |
| DIVERGENT_AUX_ONLY (recorded rule; forward and reverse) | 38 |
| COHERENCE_REPAIR (statements identical, proofs changed) | 3 |
| unexplained divergence | 0 |
| **total** | **14,101** |

The same outcomes, broken down by source label:

| Source label | byte-identical | decl-identical | AUX_ONLY | COHERENCE_REPAIR |
|---|---|---|---|---|
| UNIQUE_AT_PATH | 10,696 | 3,193 | 38 | 0 |
| RECOVERED_AT_PATH | 69 | 33 | 0 | 0 |
| SOURCE_PATH_DIFFERS | 39 | 16 | 0 | 0 |
| REPLAY_GAP_CANDIDATE | 11 | 3 | 0 | 0 |
| COHERENCE_REPAIR | 0 | 0 | 0 | 3 |

**DIVERGENT_AUX_ONLY.** The 38 modules (the 7 recorded in L187_NOTES plus 31 that the runner classified
under the same rule) differ only in auto-generated `eq_def`/`eq_unfold`/`match_N.eq_M`/`match_N.splitter`
lemmas whose `_private` module prefix is path-derived. Their imports are equal. None of their differing
constants is reached by either top theorem's raw cone (final/L187_DIFFERING_IN_CONES.json is empty).

**REPLAY_GAP_CANDIDATE.** All 14 modules with this label rebuilt byte-identical (11) or
declaration-identical (3). No replay gap remains.

**SOURCE_PATH_DIFFERS / recovered sources.** L187_SOURCE_FIXES.jsonl records 16 source substitutions:
- 12 recovered exact sources: AspisR1DotPushLocal.Funs, AspisR1EbyKFinish.Funs, NHJ_SnapshotReference.Types,
  R1LiteralTranscript, R1NaturalProjection, AspisR1WideToBytesSource.Funs, NHJ_SnapshotReference.Funs,
  ClaimsUnrolledParentTypes, CurrentWideMulExact, PowersP6IndexedOutputV1, PowersP6GeneratedErasureV1 and
  PowersP6GeneratedTotalV1. Each was recovered by object identity and receipt hash.
- 1 undetected SOURCE_PATH_DIFFERS: NJI_Extracted.Types, caught by import coherence (NJI_V1Carrier).
- 3 COHERENCE_REPAIRs (below).

Every substituted module ends declaration-identical (or byte-identical) to its overlay object, except the 3
repairs. The 55 modules labelled SOURCE_PATH_DIFFERS are all byte- or declaration-identical.

## 3. COHERENCE_REPAIR cases

All three are proof-only. Statements are textually frozen. In the final comparison, forward and reverse,
imports and constant names are equal and `identical_except_theorem_proofs` holds. None of the changed
proofs is reached by deployed_splitB or deployed_charge.

1. **NND_Tx2Values.** Stale RSL_TX2_241 (6e526453 pre-revision vs closure 20b4032c, Revision 2/3 mapVErr
   alloc arm). The proof of mapVErr_returned gains `rs_lift ... alloc`.
   - Old source e7baa401..., new 7fa4e82b... (repairs/NND_Tx2Values.lean).
   - Its cone constants (Values, Values.auth, Values.auth_ret, Values.mk) are unchanged.
2. **GammaCandidateTotalityV14.** Built against a different sampler extraction. The `rw [bind_pair_ok]`
   steps became `simp only [bind_tc_ok, ...]`.
   - Old source 1efbba2c..., new 00c02c50... (repairs/GammaCandidateTotalityV14.lean).
3. **NNH_Stage1PrepareDomain** (this session; B0076/B0077 FAIL, B0079 PASS).
   - Cause: the overlay object (receipt NNH_L701) loaded RSL_TX1_094 Revision 3. That was
     NNH_objects/RSL_TX1_094.olean a7f96619 (NNH_L103, source 924a5688), where
     `Domain := obs = none ∧ publicDom`. The closure loads Revision 4, NNO_exports/RSL_TX1_094.olean
     42bab010 (source bf8a0a10, ruling (bs)), whose Domain adds `public_bytes.length = P1880_LEN`.
   - L187_Compare between the two TX1_094 objects: imports equal; Domain and rejects_constErr differ;
     P1880_LEN and domain_needs_P1880 were added.
   - The statement of `caller` is true under the closure definitions. The new conjunct follows from
     `packet.decode`, as NNH_S1DecodeExtent.source and NNH_Stage1PrepareDomainR4.caller already prove. No
     STOP condition arose.
   - Repair: the third component is proved inline by unfolding LIBC_S1.decode. Imports are unchanged,
     because NNH_S1DecodeExtent is not in the closure. `prepare` is unchanged.
   - Old source 99b5d2d5..., new 879aa3b3... (repairs/NNH_Stage1PrepareDomain.lean).
   - Focused check (repairs/focused_NNH_Stage1PrepareDomain/): exit 0, 2.92 s, 6,787,200 KiB, swap 0.
     Axioms are standard; only `caller`'s proof differs.
   - NNH_HANDOFF.md (S4 boundary) had already recorded that this module's pair was stale. It is still in
     the closure, through NNH_ExactRemainingTypes.

## 4. Stale-import findings and the final cones

L187_STALE_IMPORTS.json covered 11,863 modules that have an object-identical producing receipt with pins:
- 138 were compiled against a byte-different dependency;
- 56 of those have a non-identical stale dependency (40 NO_DIRECT_REFERENCE, 7 REFERS_TO_DIFFERING,
  8 PINNED_DEPENDENCY_NOT_FOUND, 1 NOT_CHECKED).

In the replay, all 56 rebuilt against the closure's objects:
- 44 byte-identical;
- 10 declaration-identical;
- 2 COHERENCE_REPAIR (NND_Tx2Values, GammaCandidateTotalityV14).

The one finding with a referring constant in both top cones was JGi_QRawSourceForwardTotalityV1
(`AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs`). It rebuilt byte-identical. Its overlay term
therefore typechecks in the closure environment.

NNH_Stage1PrepareDomain was not visible to that pin audit. Its receipt pinned only 2 project objects, and
the stale RSL_TX1_094 came through the unpinned NNH_objects path. The replay caught it.

Cone check: the run-7 raw cones (NNH_L942/L943) contain no NNH_Stage1PrepareDomain.* or
NNH_Stage1PublicDomain.* constant. They do contain RSL.TX1_094.Domain and P1880_LEN (the Revision 4
definitions the closure loads) and NNH_Stage1BodyChild.args/produce, all rebuilt and compared by the replay.
No differing constant of any repaired or AUX_ONLY module is in either replayed cone.

## 5. Final theorems on the replayed objects

All steps ran in the replay workspace only, in ordinary 6G/8G swap0 TasksMax=64 scopes. The 16 GiB scope
was not used.

- **NNH8_Statements** (run 7's L941 source, sha256 4178a8d2..., unchanged; imports TAS_FinalB): exit 0,
  3.50 s, 7,011,600 KiB, swap 0. Its full output (616 lines, including the `pp.all` kernel statements of
  RPx_Deployed.deployed, deployed_splitB, deployed_charge, fail_sub_rec and NNH8_DeployedOuter) is
  **byte-identical to run 7's NNH_L941 stdout**. The four statements recorded in TAS_G0_AUDIT.json
  kernel_statements_verbatim appear verbatim. Statement diff: empty.
- **Replay combined root** final/TAS_G0_COMBINED_IMPORT.lean (`import NNH8_Statements`,
  `import TAS_FinalB`): exit 0, 2.98 s, 6,966,968 KiB, swap 0. The module name is kept so the pinned
  scanner runs unchanged. It is not run 7's combined import: modules outside the TAS_FinalB closure
  (NNN_COMBINED_IMPORT and others) were not replayed.
- **#print axioms** for deployed_splitB, deployed_charge, fail_sub_rec and NNH8_DeployedOuter (also the
  NNH8_NonVacuity lemmas): [propext, Classical.choice, Quot.sound] each.
- **Raw ax2 walk** with the pinned NNM_ProofDriver (sha256 46ee271b...ca3c, asserted before every run),
  module TAS_FinalB:

  | Root | reachable | edges | walked = collected | cone vs run 7 |
  |---|---|---|---|---|
  | deployed_splitB | 146,370 | 6,981,053 | {Classical.choice, Quot.sound, propext} | byte-identical (0b316cbb...) |
  | deployed_charge | 146,551 | 6,993,492 | same | byte-identical (4ae9686f...) |
  | fail_sub_rec | 146,371 | 6,981,148 | same | byte-identical |
  | NNH8_DeployedOuter | 146,377 | 6,981,367 | same | byte-identical |

  Walker peaks were 7,520,148 / 7,530,520 / 7,659,292 KiB, swap 0.
- **NFX scan** with run 7's pinned NNH8_RuntimeScan (sha256 58cbfe20..., unchanged):
  - The expected-imports baseline is run 7's file with only the root's line replaced
    (final/NNH8_EXPECTED_IMPORTS.DERIVATION.txt).
  - Result: exit 0, NFN_SCAN_ZERO_DANGLING. 19,864 modules, 882,507 declarations, 29,545,856 edges;
    0 dangling, 0 duplicate owners, 0 import mismatches; 3,157 cached replicas, 3,101 of them
    proof-identical.
  - 30.22 s, 8,344,612 KiB (run 7: 8,317,012), swap 0.
  - Run 7 scanned 20,019 modules. The difference is the non-closure modules its combined root imported.

## 6. Resources

| Item | Value |
|---|---|
| batches | 80 (B0001–B0080), each in one 6G/8G/swap0/TasksMax=64 scope with allowed:true admission |
| concurrency | at most 2 batch scopes; host lean count < 6 and >= 40 GB free before every launch |
| summed batch wall | 11.67 h |
| module compile rows | 14,108 PASS, 21 FAIL, 14 DIVERGENT, 12,246 NOT_RUN_BATCH_STOPPED, 266 operator-stopped |
| max lean RSS | 7,087,904 KiB |
| max cgroup peak | 5,068,910,592 B |
| swap | 0 throughout |
| final steps | 7 scopes (compare, 2 lean, 3 walker, 1 scan) |

No cap, heartbeat or timeout was raised. No failed shape was rerun unchanged. The 13 FAILURE alerts, from
B0001 to B0077, were each resolved by a recovered source, a recorded rule or a COHERENCE_REPAIR.

Correction: tools/L187_Compare.binary.sha256 first recorded c5f43e8e.... The binary in use since
2026-11-09 21:47 UTC, rebuilt from the committed L187_Compare.lean, is a758dd57.... The sidecar now
records both.

## 7. Conclusion

Coherence is established for the replayed closure. Every one of the 14,101 project modules was rebuilt
from committed source against replayed objects only. Each is byte-identical, declaration-identical,
DIVERGENT_AUX_ONLY under the recorded rule, or one of three proof-only COHERENCE_REPAIRs with statements
unchanged. No log of a credited module shows sorryAx.

Step (b) passed: the combined import compiled, the axioms are standard, the raw ax2 cones are byte-identical
to run 7's with walked = collected = {Classical.choice, Quot.sound, propext}, and the NFX scan is clean.
Run 7's theorems AspisR1.TAS_FinalB.deployed_splitB and deployed_charge (with fail_sub_rec and
NNH8_DeployedOuter) are therefore re-credited on the replayed objects, with kernel statements identical to
run 7's.

This re-credit is limited in four ways:
- It covers the TAS_FinalB closure only, not run 7's wider TAS_G0_COMBINED_IMPORT.
- It does not change what those theorems state or assume.
- It does not establish source/native correspondence or the release blockers recorded in run 7: extraction
  provenance (bk), source-to-ELF / L188, Pool boundary (aj)(a), multi-attempt accounting, the Runs
  non-vacuity witness, trust removal conditions, K086 and R22.
- Neither Lean nor NFX re-checks imported objects. The replay itself is the evidence that every overlay term
  checks in the closure environment, within the limits of the declaration comparison.

target not yet established
