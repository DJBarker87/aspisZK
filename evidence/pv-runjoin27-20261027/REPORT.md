# Runjoin27 — LOG D337 resume

**Target not yet established. Checked coverage counterexample; stop at step 1.** Worktree exactly `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch `codex/pv-runjoin-20261026`, entry revision `d6bc54e2132d785caaf0284afb11ce949539066b`. No push or merge. No shipped source, simulator, observer, wallet or key change. No XR module imported or definition copied.

## 1. Admitted full withdrawals cannot pass native preparation

The requested first gate quantifies over **every honest witness/statement in the admitted spend relation**, rather than assuming successful preparation as an additional domain restriction. It fails on a full withdrawal of the deterministic fixture's 1000-unit input:

- input value 1000; withdrawal/output value 1000; change value 0;
- original canonical fixture input key, salt, pair and 24-level membership path;
- original change owner/salt `digest 700` / `digest 800`, but the change commitment is recomputed at value zero;
- the output pair, append root and carry frontier are recomputed for that new commitment.

`R1Z.PV_RunJoin_SpendDomain27.admitted` proves the exact `BuilderSpendRelation.RspendPlus statement witness`. This supplies the full public option shape, input relation, integer conservation, change commitment, withdrawal amount and append binding. Hashes remain symbolic: `attachAppend` / `seal_append` establish the append result without reducing a whole run. `change_zero` and `positive_change_does_not_follow` prove that this admitted witness has zero change and that positivity does not follow from the adopted relation. There are no candidate premises in the admission theorem. All six new theorems have checked standard axioms.

The actual frozen withdrawal wrapper, `compile_pool_v1_pair_forest_withdrawal_merged_c1_v1`, explicitly rejects `witness.change.value == 0` with `Conservation` **before** calling `compile_forest_from_copies` (`crates/aspis-statement/src/pool_v1/pair_forest_trace.rs`, lines 468–474). `source-guard.json` records the exact body, order, source hash and git blob and checks that the file is unchanged from the resume head. Transfer has a corresponding positive-change guard. The introductory comment in `SpendRelation.lean` already distinguishes the stronger native positivity contract, but neither Rspend nor the D50 transfer-sentinel strengthening RspendPlus adds it.

Thus **no value-preserving native encoding of this admitted full-withdrawal witness can return a successful compilation through the actual outer preparation route**. This impossibility does not require a new digest-encoding theorem: any representation preserving change value zero hits this guard or an earlier rejection. We do not assume a whole native-statement/model equality to establish that value obstruction.

The optimized native probe additionally executes the real compiler with canonical concrete witness data, correctly recomputed commitments, a valid initial snapshot and matching runtime context. `pv27-zero-change-03/out.log` records:

```text
amount=250 change=750 ...
control=Ok
amount=1000 change=0 ...
full_withdrawal=Err(Conservation)
```

Both public validations and integer conservation checks pass. The zero-change commitment is `[719444933,895488824,640824513,632111586,1772288727,1555637257,1106375822,769185376]`. The control confirms the preparation route succeeds on the original partial withdrawal. No arbitrary cached payload is mutated. Native execution is measured evidence; the full admitted mathematical statement and failure of semantic positivity are proved in Lean. See `FINDING.md`, `native-result.json`, and the native receipts.

## 2. Exact consequence and owner handoff

The accepted runjoin26 V152–V154 certificate for the subtype `HonestInput` remains valid, unchanged. This finding prevents extending its advertised coverage to **all** admitted honest witnesses via the actual preparation pipeline: the full-withdrawal case produces no successful compiler output to place in that subtype.

This is not a refutation of the separate implication “if preparation successfully returns, its output satisfies HonestInput.” That successful-output implication—including Admission, both Result layers with equality to the returned payload, Checked and canonical frontier words—remains unproved in general. This run does not silently replace the requested all-admitted domain with the successfully prepared domain.

For the owner: native preparation currently needs a positive-change honest-user domain. Full withdrawals are admitted by the recorded relation but are excluded by this preparation route. The next concrete deliverable is an explicit owner decision on that coverage mismatch: authorize the positive-change domain for the claim, or authorize compiler/release work supporting the omitted cases. Only then can the appropriate general provenance-to-guards theorem be completed. No domain change or frozen-source repair is made here, and no privacy distinguisher is claimed from this domain mismatch.

Per the requested order and checked-finding stop rule, step 2 was not started. The existing source handoff supplies no RustRealRefinement conjunct or RunJoin. The common-sample complete ROMView/observer equality outside the fixed bad event (V038), concrete deployed Rust/runtime/body/world/boundary association (V045), same-coupling marginal laws, complete native effects and L1/L2/L3 associations all remain. No observer, simulator, bad event, error bound, retry or abort observation is changed.

## 3. Premise and ledger accounting

New endpoint premises removed/added/weakened: **0/0/0**. Generic contracts changed: **0**. V152–V154 retain their accepted honest-family discharge. No further row is claimed closed; V038/V045/V047 and the other native obligations retain their previous scopes. Deployed P OPEN→OPEN. T remains exactly entropy_law, entropy_kernel, observation; no T field is added.

Recount5, quoted: “Deployed PV_Src_Premises remains five fields. No deployed source-identification closure is inferred.” The accepted runjoin26 result subsequently closed the three identification fields at the designated honest family; this finding concerns coverage of that family, not retraction of that theorem. Inherited recount6 totals remain 407 rows, OPEN86, CLOSED-ON-CANDIDATE44, 400P/3T/4C. No fresh aggregate recount or subtraction from OPEN86 is invented.

## 4. Validation, retained failures and resources

Two charged Lean attempts, both accepted; 57/59 Lean attempts remain. Zero Kani and zero local Lean. All scopes were sequential MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean-M7000. Exact receipt table:

| Attempt | Target | Exit | Host wall | Peak RSS bytes | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
|38144|PV_RunJoin_SpendDomain27|0|4.47s|4200075264|0|af7ac464fa7ab7e4367a039256eab9c64873c998|
|38145|PV_RunJoin_ProvenanceAudit27|0|3.37s|4999434240|0|6b2f565b01041216b40fbb4aa213b4346422fa76|

The exact revision in each JSON receipt is authoritative; final-check verifies its git source blob and retained source snapshot. `receipt-index.tsv` records exact host wall times. The final audit prints the new witness, statement, admission and false universal positivity claim; the original HonestInput family; RustRealRefinement; the endpoint type; and axioms for all six new theorems, the unchanged honest identification and `privacy_headline_deployed`. All are subsets of propext, Classical.choice, Quot.sound.

38141–38143 were reservation refusals, charged zero, each ID retired; the mandated three-minute waits were observed. Native `pv27-zero-change-02` was also refused, waited out, and replaced by fresh name `-03`. The inherited report records 38194–38196 already used: none was reused; the final audit used unused focus ID38145. Remaining unused focus IDs38146–38193 are recorded in tally.json.

Native `-01` exited101 after 40.074s, peak951521280bytes: the probe was missing two explicit Rust type imports. The source, committed revision, compiler errors and receipt are retained. The corrected `-03` exited0 in0.306s, peak196710400bytes. Both were `cargo run --release`, with the same caps and zero swap. Expected time was optimized compilation, then the named compiler control/rejection steps; no dense arithmetic gate. This ordinary changed-candidate failure was not a stop. No timeout, memory kill, cap increase or unchanged failed resubmission occurred.

Before first compile all5673 actual external objects matched h4/SCOPE and its official manifest hash. The final closure resolves1387 project modules under EJR/freeze/h5/h5-prime precedence, with no unpinned or XR module. The h6 checks cover669 reused replay roots and785 transitive source/object fingerprints with matching toolchain and import prefix. Private retained cache only; no shared source or another job's objects written. This is focused compilation/axioms evidence, not a new release rebuild or full manifest replay.

Native source preflight initially detected that the retained old native snapshot had the pre-owned-rewrite records mapper. The mismatch and diff are retained. The execution used an isolated source snapshot with that one file restored byte-for-byte from this worktree, and prechecked147 crate/writer source files and Cargo manifests against this revision. No shipped source was edited. The native measurement does not inherit an unverified old mapper variant. The existing optimized cargo cache was reused.

`final-check.py` validates accepted Lean source/axioms/receipts, native source snapshots and observed results, resource caps, refusal intervals, no forbidden imports and unchanged crates/programs. `commits.txt` records path-limited commits from the resume head through the proof/tooling stages; the final evidence commit follows. Stop is the checked admitted-domain/preparation counterexample, not budget exhaustion or a failed candidate. The privacy target remains unestablished.
