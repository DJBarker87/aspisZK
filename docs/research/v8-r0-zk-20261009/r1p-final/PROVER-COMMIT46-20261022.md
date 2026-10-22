# Prover commitment continuation 46

Target not yet established. Base 4a7c0512e (LOG D158), branch
`codex/cx-prover-commit46-20261022`. Work proceeds under D158's explicit
state-passing interpretation of ProgramOne; no interior-mutability trust law
is authorized or introduced. D143 observables, the D146 statement domain,
and adversarial environment/public nonce remain the intended contract.

## Stage 1: ProgramOne state transition

The retained native harness copies the shipped `ProgramOne` and concat bodies
verbatim. BTreeMap insertion is substituted by the existing D133 per-key
contract: arbitrary prior value, exact replacement, and an untouched frame.
The Kani comparison checks the digest, complete represented map update,
sticky collision flag, and a fresh mutable borrow after return. This does not
verify B-tree internals or arbitrary address lengths; the independent Lean
map/concat interface is responsible for those universal parts.

The owned reference has an explicit `ProgramState { table, collision }`
argument and returns the digest and updated state. It retains repeated writes
and unequal old-value collisions. No shipped file has been edited.

## Remaining stages

Complete publication, source-to-FSExperiments conversion, shippedProverExperiment,
both WholeRunJoins, and deployed endpoint premise removal remain pending.
No release/privacy closure claim is made by this checkpoint.

`ProverCommitProgramOne46.call_exact` proves the extracted state-passing
operation returns exactly the updated table and collision flag for every
map state, answer and parts value. `reference_decode` / `call_decode` use
only the existing insert-state and insert-previous TrustedStd fields;
`continuation_exact` reuses the part-28 generic monadic install theorem.
`ProverCommitProgramLog46.run_exact`, `expected_decode` and
`publication_consumer` thread the complete ordered log through publication,
including duplicates and the final flag. `append` composes tree logs without
resetting state; `sticky` retains every earlier collision. These are caller
transports, not a claim that codecs or multiproof generation have been joined.

Native per-call Kani passes (14.795 s, 1,608,816 KiB peak RSS, zero swap).
The first launch was rejected by the Kani CLI before compilation for a missing
unstable-options switch; v2 corrects the command. Charon and Aeneas translation
of the owned reference pass, and the two generated modules compile at
J9637–9638. J9641 and J9643 accept all eleven new bridge/log theorems; their
axioms are subsets of [propext, Classical.choice, Quot.sound]. J9639, J9640
and J9642 are rejected proof drafts, retained as failures, never accepted
as evidence. Full section-6 fields, source hashes, dependency fingerprints,
commands and axiom lines are in `../../100bit-spend-path-20261013/evidence/
prover-commit46-20261022/lean/attempts.json` and the adjacent native receipts.
No new TrustedStd field or other trust item is introduced.

## Stage 2: binary multiproof components

The binary parent group has a finite owned reference, translated through
Charon/Aeneas and checked against native generate/count group logic. The full
sixteen-entry cursor transition also passes: arbitrary strictly increasing
prefix, live cursor and write cursor; exact consumed count, parent, sibling
request and missing-node count; untouched unread suffix after the count-array
write. This is one transition, not a monolithic multiproof gate.

`ProverCommitBinaryGroup46` proves the extracted group equation and symbolic
list-layer/count agreement; its eighteen-level reference emits exactly 32
bytes per counted missing node. `ProverCommitBinaryCursor46` proves the
finite owner reaches the list layer with fuel bounded by input length.
`ProverCommitBinaryInvariant46` proves strict parent order and nonincreasing
occupancy. These results do not yet identify the complete native array/count
loops or their well-formedness guard with that reference.

`ProverCommitTreeSupport46` strengthens the tree interface: every stored
child-map domain, in depth order, is exactly the successive parent image of
the leaf map. `ProverCommitBinarySupport46.stored_requests` proves all
missing siblings requested by any batch subset are covered.
`ProverCommitStoredNode46.constructed_node` derives successful lookup from
that construction; root equality is not substituted for callback coverage.

Two pure D157 fields extend the std boundary in supplemental records in
`ProverCommitStdIndex46`: `TrustedIndex.btree_index` (BTreeMap Index returns
the associated value or panics if absent) and `TrustedSequence.vec_index`
(Vec Index returns the indexed element or panics if out of range). Both are
called at `sim.rs:360`. Consistency witnesses compile. The original shared
TrustedStd24 source/object is untouched. No source callback, interior
mutability, allocation-totality, concurrency or hash law is added.

The callback expression passes Kani under exactly these collection contracts
(1.858 s, 187,088 KiB RSS, zero swap). An initial signature draft fails Rust
compilation. A version expanding the eighteen-element Vec times out at
180 s and is excluded. The replacement uses the per-index std-contract
projection, not an unchanged retry or more RAM. The timeout expired just
before the requested stop reached cargo; kill found no such process. The
time-wrapper RSS for this failed timeout measures its parent only; the
receipt also records aggregate cgroup peak. A live observation saw cargo at
6,377,268 KiB RSS. No successful callback certificate is attributed to it.

The first group harness hit its four-iteration memcmp unwind bound; the
corrected check passes with 36. This is not a Lean resource option or a
proved counterexample. J9645 exposes a backend type mismatch from Rust's
inferred signed shift literal; an explicit `1u32` in the owned reference is
retranslated and passes a new native check. Shipped code is unchanged.
J9646 is a prelaunch dependency refusal with no compilation. Rejected Lean
drafts are retained and never treated as accepted proofs.


## Stage 2: compact codecs, byte front and finalisation

J9666 proves symbolic per-level and eighteen-level occupancy/count bounds
(≤288 nodes, ≤9,216 node bytes for a 16-entry batch). J9668 proves the native
well-formedness guard through two additional pure std observer fields in
`ProverCommitBatchGuard46.TrustedBatch`: `slice_windows2_all_lt` specifies
`windows(2).all` as an adjacent strict chain; `slice_iter_all_lt` specifies
the pure all-indices-below-bound predicate. The chain-to-pairwise implication
is proved using natural-order transitivity, not added as a source law.
Call sites are `multiproof.rs:57–58`.

`ProverCommitMultiproof46.source_bytes` / `constructed_bytes` compose the
per-group owner and the stored-node callback into exact ordered node bytes.
`reference_length` proves their count/length equation. This is the structural
P6 owner and construction invariant, not an imported theorem about Rust syntax
or a totality assumption on arbitrary child maps. Source arrays/cursors and
this owner are related by the retained native transition gates and framing
argument, as in parts 30/43/44.

A fifth pure std field is added, in
`ProverCommitCompactSource46.TrustedChunks`: `slice_chunks_exact32`, giving
ordered full 32-byte chunks and discarding an incomplete trailing suffix,
exactly at `compact.rs:113`. Every enumerated chunk index is proved in bounds.
The full compact-value owner retains the initial divisibility rejection,
every high-half rejection, low-half bytes and output length. The native
32-byte cell gate from part 43 is reused unchanged; it is not rerun or claimed
as a complete source codec by itself.

`ProverCommitCompactRows46.compact_source` composes all 27 semantic rows,
frames and payload slices, the initial 13,831-byte guard and final cursor
check. Slice capacity follows from the fixed small metadata sum, not a
source-success premise. The native row-context gate passes (1.060 s,
144,464 KiB RSS, zero swap): arbitrary u8 row, current cursor ≤13,831,
identical exact slice windows and append order, and the same arbitrary
compact_values result/post-state, including error. Its row body and
`row_shape` body are verbatim; pure std slice/Vec plumbing is projected to
window identities/append history. This is the contextual congruence cut;
the separate cell/chunk proof supplies codec behavior.

`ProverCommitFront46.proof_source` assembles the exact S2 header, compact
semantic and y1 bytes, raw suffix, ordered repeated query payloads, slots,
and both 28,359/57,607-byte guards. It retains explicit node-result slots;
the multiproof owner above supplies the concrete node-byte component.
`ProverCommitFinalize46.finish_decode` preserves replay errors/disagreement,
Merkle collision rejection, first-conflict ordered transcript merge, exact
returned table and all returned counters. `programming_publication` feeds
that finalizer the complete updated ProgramOne table/flag after its ordered
call sequence. No digest-return equality is substituted for shared effects.

These establish deterministic publication components and their structural
owner equations over raw source fields and the named std API. They are **not
a complete sim_e/source-view image or source-to-FSExperiments certificate**.
No new cryptographic or source-callee success assumption is introduced. In
particular no field assumes canonical native opening values, a mathematical
payload image, or equality with simE. All five additional std fields and their
call sites are listed above; the original TrustedStd24 remains unchanged.


## Demonstrated next interface: concrete source-view byte image

**Target not yet established.** The next required interface is not another
collection method. `ProverCommitFront46.Fields` is a raw-byte carrier;
`sim.rs:236`'s `View5`, `sim::semantic` at :248 and `sim::opening` at :335
are the actual producers. Their concrete source-to-model image has not been
installed. In particular, the byte payload `y1` at :339 must be identified
with the canonical mathematical opening values, not merely fed as an arbitrary
byte argument into a proved codec. The same image must fix the semantic rows,
remaining opening fields, packed leaf values and ordered query/node data.
The retained transcript-walk certificate concerns the walk over records;
it is not a certificate for these payload-producing functions.

This boundary is demonstrated rather than repaired by an assumption:
`ProverCommitCodecImageGap46.codec_accepts` accepts a zero-high cell whose
first little-endian low word is exactly 2^31−1. `no_canonical_first_image`
and `codec_does_not_supply_image` prove that codec success does not imply
even the necessary canonical first-word image (Fin (2^31−1)). The native
fixture retains the actual compact_values and M31/CM31/QM31 parser bodies
verbatim: compact_values returns Ok with sixteen bytes, while the actual
QM31 parser returns None. The optimized fixture exits 0 (0.151 s,
133,732 KiB RSS, zero swaps); J9684 accepts all five finding theorems,
standard axioms only. This is **not a claim that the simulator emits this
cell**, and not a privacy attack or a Rust codec bug. The codec intentionally
checks zero high halves, leaving canonicality to producer/consumer contracts.
It is a counterexample to using the generic raw-byte certificate as the
missing typed source-view image.

Exact next deliverable: prove the concrete source producer/serialization
bridge for sim::semantic and sim::opening, starting with the y1 expression
`encoded(coefficients.iter().map(|m|eval_message(m,z1)))` at sim.rs:339.
Relate every generated value and its actual to_le_bytes output to the
mathematical simulator payload, including canonical limb/high-half and length
invariants. Then instantiate the publication owner with those actual fields
and actual leaf/node request logs, and transport D143's published bytes and
observer-owned oracle history into FSExperiments. A pure std field cannot
assert any of these source arithmetic, value-provenance or simE equations.
No such field, source-success premise, caller-equality assumption or silent
raw-input-domain narrowing is introduced.

I stop at this source-image interface under the requested obstruction rule.
The complete native simulator certificate, source-to-FSExperiments conversion,
shippedProverExperiment, both concrete WholeRunJoins and endpoint premise
removal remain open. The structural publication equations above must not be
promoted to any of those claims. D143's timing/side-channel exclusion and
D146's source-representable public-statement scope remain the intended
contract. The existing environment/public-nonce models remain adversarial;
no environment probability charge, nonce law, ledger cap or new adversary
restriction is introduced here.

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
