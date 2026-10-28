# pv-runjoin16 / D287 final report — 2026-10-27

Stopped at **100/100 Lean compile attempts**:66 accepted,34 rejected; ten host admission refusals and one local deadline hold charged zero. Kani0/2 (control-only; no arithmetic SAT route used). All used IDs are tallied;50600–50707 and50897–50899 are retired, including local hold50695.50708–50896 remain unused; no compile is authorized without a renewed budget. **Target not established.**

Branch `codex/pv-runjoin-20261026`, worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, entry `f44d7c5a42`. Last shipped Rust edit: `b0e970d95029f53ed05ff51c8756254486957d24`. Proof-stage head before this handoff: `0e830d9a5c`. The closing handoff commit contains the combined audit and this report. Exact compiled source bytes, parent working-tree revisions and imported object hashes are retained in every receipt/snapshot.

## Repairs and boundary

The sole changed shipped path is `crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs`. All edits and justifications are verbatim in [REPAIRS.md](../pv-runjoin14-20261027/REPAIRS.md), entries16–26, retaining prior repair history:

- 16: D287 moves `pair_empty_roots()` to the single `CopyRecords::new` caller and adds `[Digest;21]` to `records`.
- 17–20: bounded word-loop/local-zero/owned-closure trials; the closure route stopped and was removed.
- 21–23: explicit super directions and a lexical owned mapper, with recipient dispatch.
- 24–25: lexical eight-word `raw_owned` and final straight-line owned mapping/recipient dispatch.
- 26: explicit u32 shift counts0..19, preserving all values and shift bounds.

Final `records` contains no root-helper/hash call: it uses lexical `raw_owned`, an owned Copy argument mapper, fixed-array literals and the terminal recipient match. The caller computes the same root table once and passes it. Existing global `raw`, `pair_empty_roots`, and Poseidon helpers remain untouched. Copy derives are recorded at field.rs22, pair_trace.rs71, pair_forest_trace.rs53, payment_relation.rs88 and pair_tree_profile.rs403. The module is excluded for Solana at pool_v1/mod.rs21–22. [Source audit](source-freeze-audit.json) verifies the exact authorized exterior diff and all510 host build inputs. Shared env-J sources were never written.

The abandoned closure candidate hit `core::ops::function::FnOnce::call_once`, `/rustc/library/core/src/ops/function.rs:250`, missing from LLBC. Minimal alternatives were extractor monomorphization support or removing that closure inside `records`; the route stopped and repair20 chose the latter. [Exact blocker/receipt](CLOSURE-ROUTE-STOP.md). No outside-helper source or extractor change was made.

## Gate (a) and extraction

After the final Rust change, all three SBF builds exited0, swap0, and matched:

| ELF | SHA-256 | Bytes | Wall s | Peak RSS KiB |
|---|---|---:|---:|---:|
| default | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 |1563728|36.527|684152|
| devnet |63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299|1563728|34.667|684156|
| Pool |121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548|605704|33.192|679264|

[Final gate receipts](gate-a.json), `shifts-*/receipt/receipt.json`. No shipped Rust changes followed. Gates(b)/(c) remain the lead-owned [combined plan](../pv-runjoin13-20261027/GATE-PLAN.md); neither was run here.

Pinned, unchanged Charon/driver/Aeneas completed extraction with preflight ON: `pv16-records-charon-15` exit0,20.021037s,1330470912bytes RSS,swap0; `pv16-records-aeneas-15` exit0,11.761748s,730263552bytes RSS,swap0. Both source revision b0e970d950. Tool SHA-256 pins are in their receipts. LLBC `074f08b264882def1602bcc454272dead678072f3354b05365851fcbdd07685b` is retained on the host; preflight reports has_errors=false, concrete records/local bodies. Generated source was changed only for import-path normalization: [receipt](generated-import-normalization.json). Generated types/functions passed50601/50603; their unchanged files print no initial axioms result, so the generated root was audited explicitly in50898 ([link](generated-audit-link.json)).

`R_shipped` is the nominal adapter around that concrete extracted `records`, parameterized by the root table. It is not the earlier safe-reference dictionary.

## Proved and open

| Obligation | Transfer | Withdrawal | General |
|---|---|---|---|
| Extracted `Records.call R_shipped ... = PV_Src_RecordDynamic.call E_shipped ...` |PASS50607|PASS50611|PASS50629, all arguments; arbitrary-table version also proved|
| Exact records/CopyRecords return |PASS50635|PASS50635|dictionary/newRecords transport50631|
| First selected-commitment comparison |PASS50652|PASS50652|fixture arguments only|
| Pair leaf/source validation; native path levels1,21,24 |PASS50688/50690|PASS50688/50690|symbolic lift plus24 checked node certificates|
| Record nullifier, recipient/change commitments |PASS50643/50700|PASS50643/50700|source record computations|
| Compiler-return equation at actual selected i |OPEN|OPEN|transport only; success not inferred|
| Full selected-i transition equality |OPEN|OPEN|not supplied by record packing|
| Deployed public binding |OPEN|OPEN|no installed selected input fabricated|
| P ∧ hypothetical T non-vacuity |OPEN|OPEN|T not instantiated/expanded|

The exact read-only source-root binding is **`R1Z.PV_Src_RootHelper.source`**:

```
@BuilderForestAdmissionPort.pool_v1.pair_trace.pair_empty_roots
  PV_Src_ExternalReference.dictionary = ok PV_Src_CanonicalRoots.table
```

`E_shipped` abbreviates that dictionary. The theorem consumes RootCertificate.source_eq, RootCell00.source and RootParents.source (21/21 source cells), pinned in [root-binding.json](root-binding.json). HoistedCaller16.frozen/original (50703) proves the authorized caller composition using this binding; it is explicitly a structural composition, not another caller extraction.

All24 membership-node and nine output-note permutation certificates passed;759 new named single-round equations avoid concrete recurrence reduction. The symbolic constant-callback full source permutation passed50707. The production `format.pool_v1_nullifier` loop remains to be composed separately; its result is not inferred from the record-nullifier check. Output-pair/append candidates match numeric probe values but remain **uncompiled candidates**, separated under `candidate-certificates/`. Uncompiled HashCallback16/CompilerChecks16 drafts are under `drafts/`; they establish no theorem. All generators' --check validations pass.

## P, T and focused audit

Constructed P before→after: `{source public binding, trace}`→same. Deployed P: OPEN→OPEN. Record counts: **2/8/6→2/8/6**. Endpoint premises removed0, added0, weakened0. `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` still requires its deployed RustRealRefinement and existing deployment conditions. Prover/shipped identification, E1/E2, real RunJoin, L1/L2/L3, client proof-account binding and complete observer obligations are retained. simE/observer/endpoint source files are unchanged.

T remains exactly **entropy_law, entropy_kernel, observation**, hypothetical. No native gap became a T field.

50898 passed the combined records/fixture audit; every printed dependency uses only propext,Classical.choice,Quot.sound.50897 failed a missing direct transfer import, fixed in50898. **50899 failed at import**, before endpoint print commands: missing `/home/dombarker/project-offloads/codex-pv-runjoin-20261026/lean-objects/AspisR1ProducerRelease47/Funs.olean`. Thus this run has no completed endpoint axioms audit. [Exact cache blocker](AUDIT-ENDPOINT-BLOCKER.md). No unchanged full regression or complete frozen-manifest replay ran; the release target remains open.

## Receipts and deviations

All host jobs used dedicated Linux scopes6G high/8G max/swap0/Tasks64, Lean-M7000. Peak Lean RSS was5384048640bytes; all recorded Lean swaps0. Mathematical generation used rustc opt-level3. [All136 host receipts](all-host-receipts.json), [all100 Lean receipts](receipt-index.tsv), [tally](tally.json), [accepted source-byte inventory](proof-status.json). The formal theorem audit is50898; native/SBF/generator receipts mark axioms N/A. Representative exact receipts:

| Attempt / target | Exit | Wall s | Peak RSS bytes | Swap | Source revision | Axioms |
|---|---:|---:|---:|---:|---|---|
| 50603 / `R1Z/PV_RunJoin_RecordsFuns16` | 0 | 3.924202 | 2890534912 | 0 | `b0e970d950` | standard (audited50898) |
| 50607 / `R1Z/PV_RunJoin_TransferIdentification16` | 0 | 2.942765 | 4362522624 | 0 | `b0e970d950` | propext, Classical.choice, Quot.sound |
| 50611 / `R1Z/PV_RunJoin_WithdrawalIdentification16` | 0 | 2.755240 | 4384083968 | 0 | `b03213bc7c` | propext, Classical.choice, Quot.sound |
| 50629 / `R1Z/PV_RunJoin_GeneralIdentification16` | 0 | 2.700468 | 4327772160 | 0 | `7d79aeb30c` | propext, Classical.choice, Quot.sound |
| 50631 / `R1Z/PV_RunJoin_CompilerDictionary16` | 0 | 2.240194 | 4328472576 | 0 | `7d79aeb30c` | propext, Classical.choice, Quot.sound |
| 50703 / `R1Z/PV_RunJoin_HoistedCaller16` | 0 | 2.215213 | 4337651712 | 0 | `cb5b23185f` | propext, Classical.choice, Quot.sound |
| 50690 / `R1Z/PV_RunJoin_PathChecks16` | 0 | 2.845854 | 4414799872 | 0 | `aeb3e874cc` | propext, Classical.choice, Quot.sound |
| 50700 / `R1Z/PV_RunJoin_OutputChecks16` | 0 | 2.944929 | 4413894656 | 0 | `cb5b23185f` | propext, Classical.choice, Quot.sound |
| 50707 / `R1Z/PV_RunJoin_CallbackPermutation16` | 0 | 2.032168 | 4279205888 | 0 | `cb5b23185f` | propext, Classical.choice, Quot.sound |
| 50898 / `R1Z/PV_RunJoin_TrustAudit16Records` | 0 | 2.156861 | 4417609728 | 0 | `0e830d9a5c` | propext, Classical.choice, Quot.sound |
| 50899 / `R1Z/PV_RunJoin_TrustAudit16Endpoint` | 1 | 0.746875 | 1341190144 | 0 | `0e830d9a5c` | not reached: import failure |


50643 was launched about22seconds before the mandatory three-minute deadline; [deviation](WAIT-DEVIATION.md). The private launcher now enforces the deadline before admission/ID consumption and requires both allowed:true and exit0. Local hold50695 demonstrated the guard and was retired without a host launch. Dependent50706 was mistakenly queued before failed50705 was inspected; it failed immediately on the absent object and is charged ([deviation](DEPENDENT-LAUNCH-DEVIATION.md)). No rejected object/proof was consumed. All historical failures remain recorded.

All nine task-created SBF build keys remain on the host, mode0600; no cleanup/refund was attempted ([retention](key-retention.json)). No keys, ELFs, binaries or oleans are committed.

## Next concrete deliverable

With renewed authorization/budget: specialize the checked constant-callback source permutation through the actual two-chunk production-nullifier loop on the fixture inputs; then close output-pair/late-append/bank validation and prove the exact compiler-return equation at the actual selected i. Compose the returned transition/public binding and P∧hypotheticalT witness only after that. Resolve the missing producer object through the EJR/rebuild2 source authority, privately restore/build its exact cohort, and finish the endpoint audit. Keep the lead's combined(b)/(c) gates pending; never enlarge T.

## Commit stages

`git log --oneline f44d7c5a42..HEAD` before the closing handoff commit:

```
0e830d9a5c Prove native output commitments and hoisted caller composition
cb5b23185f Prove native fixture membership path and pair leaf checks
aeb3e874cc Prove fixture path inputs and bounded source checks
353ab3c642 Prove concrete extracted record returns and input leaf checks
5fe825bbeb Prove general extracted records identification and compiler transport
7d79aeb30c Prove withdrawal identification and finite array shapes
b03213bc7c Check concrete records extraction and transfer identification
b0e970d950 Type records constant shift operands as u32
e5de9c9b56 Retain concrete records extraction for kernel checks
dc8f3093d8 Dispatch recipient before concrete owned records mapping
b4e1c2ae3a Factor records projections into lexical owned helper
65c34b4f38 Use owned local mapper with terminal recipient dispatch
475fe95745 Use direct owned subitem inside records body
8a4fa1b45a Expand records super direction assignments
f6ea02e1a7 Stop closure route and capture records loop fields
e5f6e395e1 Retain extraction diagnostics and bounded loop repair receipts
11537a57a7 Isolate records loops in owned local closure
34eea9639f Construct records zero arrays locally
e8bbf8c471 Bound records word projection with local loops
fff0730b64 Record matching ELF pins after empty root hoist
aa906c68dc Hoist records empty roots to CopyRecords constructor
```

The closing handoff commit adds the final audit, receipts and report; it changes no shipped implementation or checked theorem body.
