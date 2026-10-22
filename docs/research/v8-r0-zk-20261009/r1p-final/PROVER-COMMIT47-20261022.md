# Part 47: owned y1 evaluation and byte image; native-generator target remains open

**Target not yet established.** Branch `codex/cx-prover-commit47-20261022`.

Scope: concrete `sim::semantic` and `sim::opening` bytes, starting with y1,
then complete native simulator payload equality. Stop before FSExperiments
conversion, shippedProverExperiment, joins, or endpoint changes. D159 includes
L1 side-channel observables; the concurrent audit owns that definition.

No shipped file is changed. No new trust item or premise is authorized.
The endpoint before/after snapshots in
`evidence/prover-commit47-20261022/endpoint/` are verbatim copies of part 46.

## Stage 1: producer range and encoding

The raw codec counterexample in part 46 is retained. The actual y1 producer
embeds QM31 messages and point coordinates into WideExact, then evaluates
with addition and multiplication. The required invariant is the canonical
QM31 subfield image, rather than arbitrary codec success.

J9693 and J9696 compile the exact-field subfield and evaluator identities.
`ProverCommitEval47.message_model` identifies the natural-basis dot product
with the retained `R0.Chord.evalMessage` at every circle point. The y1 range,
canonical limb tuple, zero high half, full decoding and compact-cell equations
hold for every 29-lane QM31 coefficient family and QM31 point. These are
mathematical producer-shape facts, not yet a native source-to-payload image.

The actual copied Rust field bodies pass Kani `embedded_codec` (6.375 s,
569888 KiB, zero swap) and `embedded_add` (0.723 s, 164212 KiB, zero swap).
`embedded_mul` times out at 180 s, no verdict. It is not rerun unchanged.
The timeout wrapper RSS is parent-only; cgroup peak is retained separately.
No multiplication or whole-generator certificate is attributed to that run.

## Stage 2: extracted primitive arithmetic

The literal release arithmetic/serializer translation succeeds, but exposes
array-iterator and mutable-chunk external templates for the serializer.
Those templates are retained as diagnostics, not installed as axioms.
A second, narrower translation of arithmetic only uses overflow checks and
has no external templates. Checked/release agreement remains a separate
obligation. No unchecked arithmetic result is silently substituted.

J9743 transports the checked CM31/QM31 arithmetic to the retained canonical
arithmetic results. J9746 proves checked embedded WideExact add/mul closure.
J9749 proves successful checked scalar operations equal wrapping operations.
J9754 composes that relation through all needed field layers, including the
actual release WideExact multiplication. J9756 discharges the checked-success
intermediate: actual release `from_qm31` normalizes every raw input and
preserves its exact value; actual release add/mul preserve the canonical
QM31 embedding and have the expected exact field value. No checked-success
premise remains in `ProverCommitNativeOps47.add_exact` / `mul_exact`.
This replaces the timed-out direct multiplication gate with kernel proofs
over both extractions; no larger cap or unchanged retry is used.

The release serializer's external templates are not installed. D157 is not
used to assert a source arithmetic or payload-image law. No std field has
been added in this stage. Only new task-owned source/object overlays have
been installed; previous versions are snapshotted in the branch workspace.

## Stage 3: complete owned evaluator and canonical limb image

The D144 counter references are in `pair-owner/lib.rs` and
`basis-owner/lib.rs` in this task's evidence directory. Each loop is a
separate recursive function over owned arrays and a decreasing counter.
Charon/Aeneas accepts both. Their extracted field callees are rebound to
`AspisR1ProducerRelease47` only after `bind-counter.py` / `bind-basis.py`
compare every reused declaration body byte-for-byte; the bindings and full
generated inputs are retained. No external template or new std field is used.

`ProverCommitPairCounter47.source_finite` and
`ProverCommitPairValue47.source_value` prove all 512 pair iterations,
including every array index, canonical arithmetic result, and exact decoded
dot product. `ProverCommitBasisMath47.block` proves the symbolic next-block
identity. `ProverCommitBasisCounter47`, `ProverCommitBasisFillValue47`,
`ProverCommitBasisStep47`, and `ProverCommitBasisValue47.values_exact`
prove the nine-stage basis reference produces canonical values equal to
`naturalLineValue` at every one of its 512 positions. No Finset.univ or
concrete 512-step recurrence is reduced.

`ProverCommitY1Owner47.raw_value` composes these owners with the retained
natural-basis model. Every raw coefficient/point family is normalized by
the proved constructor; the result is canonical and decodes to the model's
message evaluation. It has no codec-success, source-success, basis-value
or caller-equality premise. It is explicitly an **owned-reference theorem**:
it does not assert identity with `sim::opening`, the native iterator loops,
the concrete simulator tape, or the complete model payload.

`ProverCommitWordBytes47.word` identifies the backend u32 byte encoding
with the retained exact little-endian codec. `ProverCommitLimbBytes47`
proves each canonical source limb's bytes, its complete 32-byte canonical
subfield cell image, exact decoding, and compact-cell equation. The actual
Rust `WideExact::to_le_bytes` byte-order gate also passes for arbitrary
canonical QM31 inputs: 2.863 s, 288704 KiB RSS, zero swap. Its eight limbs
are in the same documented order, with four zero high limbs. This is a
primitive serializer gate, not a generator-payload certificate.

### Failed paths and replacements

The exact original `basis::values`, `encoder::eval_pair`, and
`encoder::eval_message` bodies are retained in the y1 extraction kit.
The generic Aeneas run exits 2 with `Not_found` in
`InterpReduceCollapse.ml:1991` / loop context joining. Specialization exits
2 at the canonicalization closure (`field/wide_exact.rs:287`,
`InterpStatements.ml:759`). Cutting after the point embedding removes that
closure but exits 2 at `eval_pair`'s `chunks_exact(2).zip(basis)`
(`r0/encoder.rs:6`, `InterpUtils.ml:151`). No source-to-owner equality is
invented from those failures. The first kit draft fails Rust compilation
because its function slicer selected `doubled_factor` instead of `double`;
the corrected source and original failure are distinguished.

The first recursive Vec-pop owner translates with a Vec::pop external
template. It is replaced by the owned-array counter above; no std trust
field for a reference-only pop call is added. The separately translated
basis owner is also array/counter-based.

J9764 and J9766 exceed the fixed kernel memory limit (peak RSS 7170100 and
7170508 KiB respectively, zero swaps) in a combined subtraction declaration.
They are not retried unchanged or with more memory. The replacement isolates
the symbolic raw source step (`ProverCommitSubRaw47.raw`) and the four
coordinate equations (`ProverCommitSubDecode47.coordinates`). J9767 and
J9769 check those separately below 3 GiB; J9771 composes them below 4 GiB.
A byte-word draft is rejected by the kernel with a scalar-width application
type mismatch (J9786). The replacement proves a pure `BitVec 32` byte lemma
and only then transports the scalar wrapper; J9788 passes. Rejected drafts,
including their nonaccepted axiom output, remain in the receipts and are
never imported as accepted evidence.

## Stage 4: pointwise y1 byte composition and stopping boundary

J9798 checks `ProverCommitY1Bytes47.component` / `every_lane`: for every
raw coefficient family, raw x/y pair, and each of the 29 lanes, the normalized
owned evaluator returns a canonical value whose complete 32-byte cell decodes
to the exact wide natural-message evaluation. The source range comes from
constructor normalization and the proved arithmetic/basis/evaluator owners.
No codec-success or model-image premise is supplied. This establishes the
**reference's** pointwise y1 byte image. It is not a theorem that the actual
`sim::opening` caller executes that reference or that its coefficient/tape
provenance is the complete simulator's mathematical payload.

An attempted larger 29-lane encoding/compacting composition is deliberately
not accepted. J9793–J9797 are stopped with exit 143 after respectively
2:09.78, 2:07.76, 0:26.01, 2:56.63 and 1:28.25 (zero swaps, roughly 4 GiB
RSS). Buffered diagnostics exposed an ambiguous E carrier in two drafts;
other interrupted runs produce no verdict. Import/opacity instrumentation
and a smaller existential pointwise statement replace that attempt. J9798
passes in 1.73 s at 3981524 KiB RSS. No increased Lean resource option,
larger memory cap, unchanged retry, or success claim for an interrupted
aggregate is used. The abandoned aggregate source snapshots are retained.

**Demonstrated remaining obstruction and next deliverable.** The exact native
helpers still fail extraction at the loop/iterator interfaces described
above. Their recursive references now have complete arithmetic/value/byte
proofs, but the contextual native-loop-to-reference binding has not been
installed. Next: prove those native per-transition/iteration bindings under
the permitted pure std iterator contracts, connect the actual source
coefficient and tape projections, and install y1 in the publication fields.
Then prove the remaining semantic/opening/query/leaf components and the
complete native simulator output equality. No native/source equality law is
added as a hypothesis to bypass this obligation. The other components and
complete output equality requested in part 47 remain open.

The final audit uses J9799, the last number in this task's allocated range.
No attempt outside the allocation or in the side-channel audit's 9800–9899
range is used. No FSExperiments conversion, shippedProverExperiment,
WholeRunJoin, or endpoint premise-removal work is started.

D159's L1 observable is inside the required privacy contract. This work
proves no side-channel privacy law and does not adopt the superseded D143
timing exclusion. No concurrent side-channel file is edited. The retained
conditional endpoint below does not establish the enlarged D159 contract
until its missing observable/refinement joins are supplied.

## Validation scope and trust

All builds run on the dedicated host. Scopes use MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64; Lean uses -M7000. Optimized Rust extraction
uses --release and -j4 with RUSTFLAGS='-C link-arg=-Wl,--threads=4'. Kani
work is symbolic primitive checking, not an unoptimized arithmetic release
gate. Reservations are checked against the 55 GiB host limit; unavailable
slots wait before compilation. No local Lean or cold dependency build runs.

No shipped crates/programs file changes. The shipped-file rule is not
triggered; no ELF rebuild runs. Existing ELF/runtime evidence is reused only
for unchanged artifacts and does not certify a new source join. This is
focused proof evidence, not a coherent release replay. No unchanged full
regression or complete frozen manifest runs while the source image and
experiment joins remain open.

Trust remains P1, P7, TrustedStd, E1 and E2, with P6 explicit as the native
source/tool/binding boundary. No std field, cryptographic assumption,
interior-mutability law, allocation-totality law, adversary restriction,
nonce law, ledger cap, or caller-success premise is added. The source
representability scope from D146 is not silently changed or installed as an
endpoint premise. No wallet/key/fund operation, push, or merge occurs.

The exact section-6 target, source SHA, dependency fingerprint, command, exit,
wall time, peak RSS, swaps, source base/overlay revision, complete axiom lines
and failed-draft errors are in `../../100bit-spend-path-20261013/evidence/
prover-commit47-20261022/lean/attempts.json` and `lean/receipts/`. Native and
extraction receipts, command/limit records, source-body bindings and input
pins are adjacent. Historical J9700 is a prelaunch refusal, never attributed
to this task; J9747 is retired before any launcher/compile.

The narrow release extraction overwrote the checked LLBC filename. The
checked generated Lean inputs, exact flags, tool hashes and text receipts
remain retained; no hash of an unavailable original checked LLBC is claimed.
LLBC artifacts themselves and all binaries/objects remain off-branch.

## Verbatim endpoint before/after: unchanged

The complete endpoint module, including every section binder, definition,
and theorem proof, is byte-identical in `endpoint/before.lean.txt` and
`endpoint/after.lean.txt` in the evidence directory. The following verbatim
excerpts retain the x/rust binders and complete theorem statement. No D146
domain restriction is installed before the source join exists; x and rust
still have their original quantifiers. No conclusion, failure event or bound
is changed, and RustProverRefinement remains explicit.

Before:

```lean
variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After:

```lean
variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```



## Final focused audit and archive

J9799 audits all 135 newly added theorem declarations and the unchanged
conditional deployed endpoint: exit 0, wall 1.76 s, peak RSS 4122868 KiB,
zero swaps. Every accepted axiom list is a subset of [propext,
Classical.choice, Quot.sound]. The count describes audit coverage only.
`final-proof-audit.json` verifies the exact installed sources and all
dependency objects in that final receipt. The complete source overlay is
`f6c2399bb70dfeebaf26ee1ab9e89dcdce48f175`; its source hashes are recorded
in `final-source-freeze.json`. No source changes follow that audit.

`shipped-sources-unchanged.json` verifies all 491 tracked crates/programs
files against the actual task base `dfd30a6f5`, with no untracked shipped
file. `source-bindings.json` checks the copied field and literal helper
bodies. `native-source-archives.json` identifies the exact package source
version for each native/extraction command, including overwritten
diagnostic drafts; `native-attempts.json` distinguishes accepted checks,
timeouts and tool errors. `host-final-inventory.json` records hash/size
pins and tool versions. No binary, ELF, .olean, LLBC, tarball or local
target directory is committed.

Stage commits are `536f50a47`, `0e6051535`, `0fa5fde0c`, `d6c3dfe63`, and
`f6c2399bb`; the final handoff commit adds completed metadata only.
`git-log-from-common-base.txt` records history through the source freeze.
**Target not yet established; zero deployed endpoint premises removed.**
The actual native generator byte-image bridge and complete simulator
payload equality remain the next obligations, with the demonstrated
extraction/binding obstruction. J9799 consumes the last assigned sequential
compile number; no further compilation is launched.
