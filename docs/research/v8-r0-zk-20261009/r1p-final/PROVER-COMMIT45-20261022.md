# Prover commitment continuation 45

Target not yet established. Base 6143f773e8fc8bcc345b70f6d63484e701dc5b2a;
branch codex/cx-prover-commit45-20261022.

## Stage 1: D157 library interfaces

Three named TrustedStd fields are added: `btree_len` (length of the decoded
ordered entries, native usize natural image), `slice_sort_ascending` (ascending
stable merge sort of scalar natural images), `vec_dedup_adjacent` (adjacent
unequal destuttering, retaining the first equal element). Call sites:
`crates/aspis-r1-cost-probe/src/sim.rs:389` and `:493` (level/transcript length),
`:477` (sort/dedup of the batch's u32 indices). Allocation totality is not
asserted. No other trust item is added. The model instance still witnesses
consistency; it does not verify Rust collection internals.

`ProverCommitStd45` proves exact sort/dedup equality, ascending order,
no duplicates, membership and arbitrary stateful-consumer transport. The
map-length theorem identifies native length with ordered iteration. Both
root-guard outcomes and the resulting success/Merkle error are transported;
this is guard refinement, not a theorem that arbitrary trees succeed.

J9624 accepts the initial Boolean-relation spelling; J9625 accepts the final
Prop-relation spelling of the same adjacent-inequality semantics. J9626
accepts all eight new transport theorems. Exit 0, zero swaps, standard axioms
[propext, Classical.choice, Quot.sound]. Exact targets, source revisions and
hashes, dependency fingerprints, commands, wall time, peak RSS, errors and
full axiom output are in
`../../100bit-spend-path-20261013/evidence/prover-commit45-20261022/lean/`.
The shared TrustedStd source/object was overwritten and its predecessor
snapshotted under the branch-specific host workspace. Consumers must be
rebuilt against the new object before their evidence is used.

Publication, experiment conversion and endpoint remain pending at this
checkpoint. No shipped source changed and no ELF rebuild is triggered.

## Stage 2: guarded tree and transcript finalisation

`ProverCommitPublication45.guarded_eighteen_levels` composes the existing
18-level tree transport with the final length/get guard. Both success and
Merkle rejection preserve the complete children maps, coins, reads and
programming-call history. The finalisation pair `publication_decode` /
`publication_none` transports native ordered transcript merge and its
pre-merge `transcript.len()` count. Conflicting entries return no successful
table or count. These are deterministic caller equations over the std API;
they do not claim the concrete programming callback or byte codecs verified.

J9627–J9631 rebuild Publication33, Merge33, Parents44, ParentStep44 and Tree44
against the changed TrustedStd object, with branch-specific predecessor
snapshots. J9633 accepts all four finalisation theorems: exit 0, 1.25 s,
2,541,868 KiB RSS, zero swaps, standard axioms. J9632 is a rejected proof
draft (the uncompiled declaration's diagnostic `sorryAx` is not accepted
proof evidence). No admitted source or accepted sorry axiom is introduced.
Exact section-6 evidence is in the Lean receipts and manifest.


## Demonstrated next interface: ProgramOne shared mutation

**Publication remains incomplete; target not yet established.** The next
source boundary is `sim.rs:114–117`, `ProgramOne::digest`, specifically
`self.table.borrow_mut()` and the stored `(Table, collision)` effect. The
source callback overwrites its entry and sets a sticky collision flag if the
old digest differs. That flag controls the visible Merkle rejection at
`sim.rs:491`; preserving just the returned digest is insufficient.

A focused diagnostic retains the callback body verbatim (source SHA and
verbatim-body check: `program-one/interface-audit.json`). Charon succeeds
with BTreeMap and RefCell opaque. The first Aeneas pass fails on nested
borrows in the separate `concat` helper (exit 2, 0.305 s, 69,344 KiB RSS).
The changed second pass makes that already-separated concat callee opaque;
it succeeds (exit 0, 0.343 s, 69,696 KiB RSS, zero swaps), but exposes precisely
the unresolved stateful interface:

```lean
core.cell.RefCell.borrow_mut :
  RefCell T → Result (RefMut T × (RefMut T → Unit))
ProgramOne.digest : ProgramOne → Slice (Slice U8) → Result (Array U8 32#usize)
```

These are explanatory signature excerpts. The complete emitted functions
and external templates are saved verbatim as inert `.lean.txt` under
`generated/AspisR1ProgramOne45/`; **none is installed or imported**. The
return-only generated function does not return the modified shared table or
collision flag. Filling those external templates with an arbitrary pure
RefCell model would not certify source mutation. The `deref_mut` writeback
and borrow-release boundary must be represented with explicit state first.

`ProverCommitEffectGap45.returned_digest_does_not_identify_effects` exhibits
the same lawful model map/TLS instance (including all twelve TrustedStd
fields), identical digest returns, and different table entries and collision
flags. `publication_differs` shows the actual finalisation model then returns
Merkle error in one interpretation and publishes proof/table in the other.
This is an interface countermodel, **not a Rust RefCell bug**. J9635 accepts
both theorems: exit 0, 1.17 s, 2,538,600 KiB RSS, zero swaps, standard axioms.
J9634 rebuilds the existing publication/error consumer against the new map
interface (exit 0, 1.36 s, 2,550,088 KiB RSS, zero swaps).

Historical evidence was checked rather than ignored: part 20's
`table-source-empty-v2` verifies one empty-map insertion at an arbitrary
one-byte address; the overwrite-flag trials in parts 20/21 reached
MemoryHigh and are excluded. Those checks do not establish the universal
shared-state publication interface. Part 27's effectful CoinOracle bridge
has a different source callback and cannot silently stand in for ProgramOne.
The part-44 native parent harness explicitly substitutes a recording callee.

**Stopping under D157:** the standing authorization covers pure collection
and slice methods, and explicitly excludes interior mutability. No
`RefCell::borrow_mut`/`RefMut::deref_mut` field, shared-state callback law, or
source-success premise is added to TrustedStd. The lead must choose the
stateful interface at this boundary. Recommended next deliverable: follow the
existing P6 route with an owned state-passing ProgramOne reference returning
`(digest, table, collision)`, a native per-call transition check under the
accepted map contract, and Lean induction through the retained leaf/node
write log, including borrow lifetime and collision rejection. This proposes
proof work, not a new trust assumption. It has not been done here.

An independent native multiproof diagnostic also translates successfully:
Charon exit 0, 0.282 s, 189,832 KiB RSS; Aeneas exit 0, 1.588 s, 110,176 KiB
RSS; zero swaps. The full source `well_formed`, `node_count`, `generate` and
`ProgrammedTree::multiproof` bodies are retained in an isolated proof-only
crate. Its generated windows/all/Index/Option std templates remain unresolved
and inert. Successful extraction is not a multiproof refinement theorem.
No additional TrustedStd field was introduced for these diagnostic templates.
The exact commands, tools/source hashes, source revision, caps, reservation
inventory, status, wall/RSS/swap and logs are in `native-attempts.json`,
`native/` and `pins/` alongside the retained Rust input.

The complete proof bytes, concrete ordered tables, full publication and all
its early errors therefore have no complete native certificate yet. Per the
stopping rule, source-to-FSExperiments conversion, `shippedProverExperiment`,
both concrete WholeRunJoins and endpoint premise removal remain open. D143's
published-data projection and D146's source-representable statement domain
remain the intended deployed contract. Environment and public nonce remain
adversary inputs in the existing local models. There is no new nonce law,
ledger cap, privacy claim, or hidden change to the security bound.

## Verbatim endpoint before/after: unchanged

Full modules, including all section binders and the theorem proof, are
byte-identical in `endpoint/before.lean.txt` and `endpoint/after.lean.txt`.
The model statement domain and arbitrary runtime quantifier remain unchanged;
no D146 narrowing is claimed installed before the source join exists.

Before binders and theorem statement:

```lean
variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
variable (rust : FSExperiments K CommitHandle Aux R1Bat F)

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After binders and theorem statement:

```lean
variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
variable (rust : FSExperiments K CommitHandle Aux R1Bat F)

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Focused audit and artifact scope

J9636 accepts the final audit of all fourteen new theorems, the updated
TrustedStd consistency witness, and the unchanged conditional endpoint:
exit 0, 1.78 s, 4,115,484 KiB RSS, zero swaps. All axiom lists are subsets of
[propext, Classical.choice, Quot.sound]. The read-only `final-proof-audit.json`
checks the exact final installed changed source hashes and every dependency
object in the audit receipt. This is focused evidence, not a coherent formal
release replay. No unchanged full regression or final frozen manifest ran;
the source closure is not ready for that release gate.

All host jobs ran in the pinned Env J workspace or the branch-specific
extraction workspace with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0 and
TasksMax=64; Lean has -M7000. Extraction used optimized Rust compilation,
-j4 and RUSTFLAGS='-C link-arg=-Wl,--threads=4'. No dense arithmetic gate,
local Lean/cold dependency build, uncapped job, unchanged failed rerun or
raised proof resource option occurred. Every actual compile attempt uses a
previously free number J9624–J9636; no earlier receipt is attributed here.

`shipped-sources-unchanged.json` verifies all 491 tracked crates/programs files
are unchanged from the base, with no untracked shipped source. The ELF
rebuild rule is not triggered. Unchanged artifact evidence is reused only
for unchanged artifacts. No binary, LLBC, object, ELF, tarball or local
target directory is committed. Generated diagnostic templates are inert
text, with their emitted axioms never accepted into Lean. No key/wallet
operation, push or merge occurred.

Stage commits: 55d077331 (three std fields and exact library transport),
ded8379e1 (guarded tree and transcript finalisation). The final commit retains
the stateful-interface finding and all audit evidence. The named trust list
remains P1, P7, TrustedStd, E1, E2; P6 remains an explicit native/source evidence
boundary. **Target not yet established.**

The final staged whitespace check reports only bytes retained verbatim from
native tool output: four generated-template blank EOF lines, one blank EOF
in the failed Aeneas stdout log, and one trailing-whitespace line in its
exception stderr. These are raw evidence, not proof-source whitespace defects.
`host-jobs-finished.json` confirms no branch-workspace process remains.
