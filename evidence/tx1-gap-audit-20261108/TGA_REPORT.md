# TGA_ TX1 345/344/333/330 spec-versus-library gap audit

Target not yet established. This audit is read-only with respect to every row
artifact. It closes no row and claims no credit. Its purpose is to find the next
blockers of the P1880/F9 kind before NNG_ reaches them.

Inputs (research at f7ccfbace7a): RSL rev4 (evidence/rowspec-lead-20261107;
RSL_TX1_094 bf8a0a10, RSL_TX1_328 6d0f98a1, RSL_TX1_345 0c360454, RSL_TX1_344
48399130, RSL_TX1_333 dfa7dbf5, RSL_TX1_330 466efb55, RSL_Base 4fb94e7d,
RSL_Verifier e6f9a448); LIB_ (lib-20261111, F9 state), LIBC_, LIBB_; NMV_
(stage-wrap-20261111); NNF_ (entry-rsl-20261111); NNG_ (tx1-principal-20261111);
ledger27 NNK_REMAINING. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:
programs/r1-cost-probe/src/{r1_pool_adapter_owned.rs, r1_pool_adapter.rs,
lib.rs, pool_route.rs}, crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs,
crates/aspis-r1-cost-probe/src/verifier.rs.

## Summary

| # | Row(s) | Finding | Class | Owner |
|---|---|---|---|---|
| G1 | 344, 333, 330 | NMV_ and NNF_ folds were compiled against RSL **revision 1**, not rev4. Rebuilt against rev4, the folds themselves still compile, but three NMV_ no-write modules fail, and those failures break NMV_TasRoots/NMV_CandidateRoots (the TAS field344 and packet). A three-file patch has been verified. | (iv) mechanical obstruction to instantiation, not a spec error | NMV_ (or NNG_ as integrator) |
| G2 | 333, 330 | These rows cannot close after 345/344 alone. RowSpec_333 = RowSpec_221 covers both routes, so process_tx1 needs RowSpec_240 for I.f240, which needs TX2:241 → 242 → 233, all OPEN (233 is "NOT A CANDIDATE" in ledger27). | (iv) real dependency. The spec is deliberately whole-function; no spec change is recommended | lead (scheduling) |
| — | 345, 344, 333, 330 | Clause by clause, no child-`dom` mismatch, Err-arm mismatch or allocation/abort-arm mismatch was found. | none | — |

## G1. Stale RSL revision in NMV_/NNF_ objects

Evidence. NMV_INPUTS.json / NMV_EXPORT.json / NMV_L029-L031 pin RSL_TX1_345
8beeb59c, RSL_TX1_344 b0d269ef, RSL_TX1_094 37201f61, RSL_TX1_328 fbcf2ddb,
RSL_Base ea9f7f16 and RSL_Verifier d0cf0814. These are the hashes of commits
8e8929267ee/d5e5f1f6431, i.e. revision 1. NNF_SEED.json.xz seeds its RSL .olean
files from NMV_objects with the same rev1 source hashes. NNG_REV4_REBUILD_PLAN.json
rebuilds RSL_TX1_344/333/330, TCK_WeakRoot0, TAS_Interfaces and LIB_Instances
at rev4, but it lists no NMV_ or NNF_ module.

Why it blocks. Between rev1 and rev4, S1Lib gained `decodeReachesAlloc` (rev2),
`OwnedAccount.data`/`data_len`/`verifierCheckpoint` became RS-valued with clone
allocation arms (rev2), 241/328 `mapVErr` gained the `format!` allocation (rev2),
and VLib/Env changed in rev3. NNG_'s 345 candidate is a rev4 RowSpec_345 at
LIB_Instances.VL/P/C. It cannot be fed to the rev1 objects behind
NMV_CandidateRoots.root344 or NNF_Folds.process_tx1.

Local rebuild against rev4 (macOS arm64, Lean 4.31.0 commit 68218e87, core
only; single-file `lake env lean -o`; scratch copy, no cgroup because every job
was under 0.6 GB; full log in TGA_COMPILE.tsv):
- All 20 rev4 RSL modules: exit 0, peak RSS 695 MB or less, 0 swaps.
- These compile **unchanged** at rev4: NMV_RslLaws, RslSnapshots, RslDomain,
  RslFold (`fold344` [propext], `fold240` [propext, Quot.sound]); SdkFrame, G2,
  G2State, Window*, SdkExec, SnapshotExec, CopyExec, ConcreteWindows (holds
  `root344`/`root240`), NoWrite, NoWriteSdk. Also NNF_Folds (`process_tx1`,
  `entry_tx1` [propext, Quot.sound]), built against an NMW-free copy of the pure
  first half of NNF_Dispatch (process/entry/admitted_iff, verbatim).
- These **fail** at rev4:
  - `NMV_NoWritePool` lines 50/55/60: the `free_steps` macro has no arm for
    `RS.ofCloned`, which `OwnedAccount.data` became in TX2_234 rev2.
  - `NMV_NoWriteOwned` line 46: the same for 233's body, plus RS-valued
    `verifierCheckpoint`. Line 74: TX2_242's proof `data` is now `ofCloned`.
  - `NMV_NoWrite241` line 13: rev2 `mapVErr` allocation. Lines 26/30: the
    `data` clones.
  These failures break `NMV_G2Reference` → `NMV_TasRoots` (`field344`,
  `packet`) → `NMV_CandidateRoots.root344`.
- Fix verified: TGA_NMV_REV4.diff (sha256 prefix dea825de). It adds
  `ofCloned_free`, `data_free` and `verifierCheckpoint_free` (write-freedom:
  the clone and the checkpoint check add only an allocation, never a write),
  adds three macro arms, and edits three proof lines. With the patch, the chain
  through NMV_CandidateRoots exits 0: `root344` [propext]; `root240`/`packet`
  [propext, Quot.sound]. No sorry and no new axiom.
- Not tested locally: NMV_NNCWeak (needs NNC_G1a), NNF_Carrier/Reify/TAS (need
  NMW/Hiq Aeneas emissions). NNF_TAS is a thin wrapper over the folds, but it
  must still be rebuilt on rev4 objects.

Action. NMV_ applies TGA_NMV_REV4.diff and re-pins NMV_ and NNF_ against rev4
RSL objects before NNG_ instantiates 344. This needs one focused compile per
changed module and no proof redesign. Record the rev1 → rev4 re-pin as a source
change in each handoff.

## G2. 333/330 depend on the TX2 chain

RSL_TX1_333: `RowSpec_333 := TX2_221.RowSpec_221 … (TX1_344.asStage1 …)`. This
is the whole `process` (r1_pool_adapter.rs:950-962) over both admitted routes.
`NNF_Folds.process_tx1` takes `stage2 : TX2_240.RowSpec_240 L D V f2`.
`NMV_TasRoots.field240` gives that only from `TX2_241.RowSpec_241` for I.f241.
Ledger27 lists TX2:241 (needs 242), TX2:242 (needs 233) and TX2:233 (NOT A
CANDIDATE) as OPEN. The order after 345 is therefore: 344 closes, and 333/330
close only together with 221/213, after 233 → 242 → 241 → 240. The plan "345,
then 344, 333, 330 by instantiating folds" holds for 344 only. A single-route
333 would be a weaker theorem than the function's obligation, so no spec change
is recommended.

## Clause-by-clause checks with no mismatch found

TX1:345 (stage1_owned, owned.rs:376-414 against RSL_TX1_345.body):
- Route guard (line 377) = `badRoute`, giving Err InvalidInstructionData.
- `require_distinct_accounts` (59-72, TX1:339) is total, with only
  InvalidArgument; `require_readonly_buffer` ×2 (45-47, TX1:340) is total.
- `require_verifier_checkpoint(ck, pid, true)` (51-58, TX1:341): the
  short-circuit order and the `data_len()?` clone (`RS.ofCloned`) match.
  1768 = checkpoint_size(S2) = 744 + 16·64 (verifier.rs:18,32).
- `ck.data()?`, `require_zero` (73-79, TX1:342), and `pub.data()?`: each getter
  is `RS.ofCloned`, total.
- `decode_public_statement_box` (adapter.rs:237-244, TX1:332):
  LIBC_S1.decode is total on all Bytes (length guard at 1880 =
  pair_forest_terminal.rs:403). `NNG_Total345.decoder` shows the Aeneas
  decodeCall never returns fail/div, so the `| _ => none` arm collapses only
  Err. The internal allocation collapse uses `LIB_S1.allocation`. The outer
  Box allocation comes after Ok, matching line 240.
- Validator (TX1:276): total by NMT_R2_ValidatorTotal (NNG_ValidatorGraph345).
  Encoder (TX1:278∘267): total by NMT_R2_EncoderTotal; [u8;688], no allocation.
  semantic_public (TX1:268): pure.
- Proof checks (398-408): `checked_add` cannot overflow, and index 696 is read
  only after the length check (short-circuit), so there is no panic arm.
- first_decoded (409) at SAME arguments: publicDom comes from
  `LIB_S1.validated_public` on the validate=true arm. P1880 comes from
  `NNG_P1880Discharge`. obs = none comes from observer() with cu-profiling off.
  The proof slice length is 57607, which 094 derives after a successful total
  parse (F9).
- Checkpoint length check (410-412).
- Domain True; no caller clause is added.

TX1:344 (stage1, owned.rs:447-461): the three snapshots use lengths 58295 /
1880 / 1768 (lines 452-454). In `snapshot`, `to_vec` allocates only at an
admitted length (lines 33-35), and `snapAll_errs` makes the clone arms
unreachable. The 345 call is at SAME (program_id, owned, data).
`try_borrow_mut_data()?` returns AccountBorrowFailed. `copy_from_slice` panics
iff the lengths differ (`copyStep`). cu-profiling is off. Domain True.

TX1:333 (process, adapter.rs:950-962): the lifecycle arms 4/5/6 are excluded
by (P1) admitted. The stage1 test precedes the stage2 default, matching
`TX2_221.Ref`.

TX1:330 (lib.rs:56-65, pool-adapter): the `admitted` rejection (pool_route.rs:3-5
= `TX2_221.admitted`) precedes `process`. `NNF_Folds.entry_tx1` discharges
(P1) from it.

Propagation to the entry: 345 adds no clause (Domain True; P1880 and publicDom
are discharged internally). 344 Domain is True. 333's stage1 conjunct (P3) is
True, and 330's (E2) is True. The TX1 route therefore adds nothing at
process_r1_cost_probe_instruction. The only entry-level clause remains (E1)
Root0 on the ASQ8 route, which is owned by the headline (RSL_INDEX item 1),
together with the RuntimeEntrypointAdmission/RuntimePersistence trust rows.
These are unchanged.

## Residual integration points (not mismatches; NNG_/top must not miss them)

1. f345 must be total on all RSL `TX1_345.Args` under Domain True. This
   includes Nat lengths ≥ 2^64 and lists longer than usize. NNG_ lists this
   adapter as open. The same function must be the top's I.f345, which NMV
   `stage1 a1 I.f345` consumes.
2. The composed Impl must be `NNF_TAS.install (NMV_TasRoots.implementation I a1 a2)`,
   with I.f345 the NNG_ producer and I.f328 the function of the 328 candidate.
   Both constructions keep the other's fields definitionally, but nobody has
   built that composed Impl yet.

## Validation record

Local focused single-file compiles only (TGA_COMPILE.tsv): exit, wall, peak
RSS and 0 swaps are recorded for every attempt, including the failed rev4
attempts. Printed axioms are quoted above; all are standard. No build host, no
manifest replay, no Kani or extraction. No shipped source, RSL, LIB_, NMV_,
NNF_ or NNG_ file was edited. Patched copies exist only in the session
scratchpad; the diff is retained here.
