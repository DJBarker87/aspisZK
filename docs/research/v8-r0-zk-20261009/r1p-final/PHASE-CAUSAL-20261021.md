# Phase causality work (2026-10-21)

Branch `codex/cx-priv-phase-20261021`, base `f8b9836e0`.
Only new modules are added. BuilderSource/SourceIdentification are untouched.

## Stage 1: symbolic schedule

`R1Z/PhaseScheduleBin.lean` assigns dependency stages to every transcript and
commitment position. Bindings, seeds, both expander streams and salts precede
C1; C2 is between semantic rows 1 and 2; folded is between opening rows 29
and 30. Binary nodes increase by depth, reusing `CausalTreeOrderBin`.
Within a stage an abstract finite equivalence breaks ties. A finite linear
order isomorphism constructs `ord`; proofs use only its order laws. No
concrete position list, `Finset.univ` evaluation, or recurrence is reduced.
Mathlib's generic finite-order isomorphism is internally implemented with
sorting; it is never evaluated here. This is a noncomputable mathematical
order, not an extracted efficient scheduler.

Attempt 9000: exit 0, wall 3.27s, peak RSS 3503544 KiB, swaps 0;
four axioms audits use only propext/Classical.choice/Quot.sound.
Exact source revision/hash, launcher reservation and complete output are in
`phase-attempts-9000-9199.jsonl`. The initial runner fingerprint omitted the
Mathlib import after a failed object-path lookup. The supplemental hash is
recorded separately; a duplicate invocation was refused before compilation.
The runner now fingerprints Mathlib imports correctly and fails immediately
on a dependency lookup or launcher failure. No unchanged compile was repeated.

## Source boundary found during inspection

`BuilderSource.prover` constructs an honest trace builder, not a wire or a
decoder. `WireLengthsR1PBin.Wire` carries arbitrary byte vectors and proves
length facts only. It has no function from `JointView.view` to those vectors.
No existing definition assigning `R1Wire.frame`, `payload`, or `dec` to that
builder was found. `JointView.view` also contains arbitrary `outputs x ch`.
Thus length proofs and the builder relation alone cannot certify phase
dependencies. This must remain explicit in any final source handoff.

## Endpoint disposition

**Partial closure only.** `PrivacyR1Final.lean` is unchanged. The generic
phase interface has universal causality, and leaf/decoder/scan pieces are
constructed, but no shipped wire is proved to inhabit the interface. See the
final source handoff below.

## Stage 2: dependency refinement interface

`PhaseLocalityBin` defines `R1PhaseWire` with evaluated frame/payload/final
noninterference fields and componentwise `DecodeLocal`; `R1PhaseProver`
carries leaf noninterference and constructs both the shared binary grammar
and symbolic order from the supplied data. The old data's arbitrary caddr
and ord are discarded. `phaseDecode` constructs a block-local decoder and
`phaseDecode_local` proves its component dependencies. This construction
alone proves no sampling law or Rust decoder equality.

Focused attempt 9006 passes (2.37s, 3527080 KiB, zero swap, standard axioms).
9001 failed on a qualified circle-point type name; 9002 passed the initial
interface; 9005 passed the additional decoder contracts. 9006 changes the
prover projection to an abbreviation to expose its position types to Lean's
rewrite transparency. Complete evidence includes all failed diagnostics.
New-module source/object replacements are snapshotted per attempt under
`aspis-joint-20261019/snapshots/codex-cx-priv-phase-20261021/`. No pre-existing
module's shared source or object has been replaced. Dependent targets use
fresh object fingerprints after each dependency change.

## Stage 3: universal causality for the refinement interface

`PhaseTranscriptBin` proves every transcript coordinate is a strict stage
predecessor (including all query-advance candidates before absR), both tape
streams are available at transcript reads, and the messages' dependency
contracts suffice for transcript noninterference. Attempt 9007 passes:
3.63s, 3530696 KiB, zero swap, four standard-axiom audits. Earlier attempts
9003/9004 failed on explicit dependent parameters and rewrite transparency;
the final source fixes those without adding resource options.

`PhaseCausalityBin` proves the commitment case by the binary grammar, seed,
binding, salt, leaf and child predecessor inequalities. It then proves
`phase_causal` (`RCausal` for every refined instance at all answer vectors)
and `R_causal_D80` in exactly the position-indexed form used by the endpoint.
There is no collision, successful-run or execution-trace assumption.
9008 failed on a redundant tactic after an already solved goal; 9009 passes:
3.47s, 3519168 KiB, zero swap, three standard-axiom audits.

This is conditional on inhabiting the phase interface for the real encoding.
It does not claim that the shipped prover inhabits that interface. No
`R10_RWire_executes_phase_order` hypothesis is needed for this mathematical
causality theorem; execution correspondence cannot substitute for locality.

## Stage 4: existing-model leaf dependencies and construction

`PhaseBuilderDependenciesBin` proves the dependency lemmas on the actual
`HonestView.prepare`, `MaskLayout.applyAff`/`applyEligible`, and `Batched.q1`
functions already used in the privacy experiment:

- C1's 27 columns (0..25 and 28, matching host_commitment.rs:153–157)
  are challenge independent. This includes the mask columns, not only the
  sixteen semantic columns.
- The prepared and masked trace depends only on semantic rows 0 and 1.
- q1 depends only on gamma and alpha0 in addition to that trace. Thus the
  folded coefficient word is fixed after row 29, irrespective of later
  opening/query answers.

`PhaseLeafConstructionBin` constructs leafVal from those functions, with
separate encoder parameters for the 27 C1 columns, the two C2 columns (26,
27), and the folded coefficient word. It constructs `R1PhaseProver` data
with those leaves and proves `constructed_causal`. The remaining encoder
parameters must implement S2 coefficient transport, evaluation, four-symbol
fibre selection, field-to-byte serialization and folded padding as in
host_commitment.rs and prover.rs:218–224. Their Rust equality is not proved.
The encoder interfaces cannot receive any additional challenge or query.

Final focused attempts: 9015 (dependency lemmas) and 9016 (leaf constructor),
exit 0, standard axioms, zero swap. Attempts 9010–9012 isolate/fix namespace
and simplifier issues; 9013 passes the initial leaf constructor; inspection
of the Rust C1 list then expands its initial sixteen-column selector to all
27 source C1 columns. 9014 fails a small inequality and 9015 supplies the
symbolic arithmetic proof. Nothing evaluated a tree/position universe.

## Stage 5: prefix-dependent QueryScan construction

`PhaseQueryScanBin` constructs a first-completion scan on the eight block
indices. Readiness receives the endpoint and zero-extended observed prefix;
block 7 is the exhaustion/default endpoint. Both the selected endpoint and
decoded queries are proved invariant under changing blocks after that
endpoint. `wireData` installs this scan and the component-local challenge
decoder in an existing wire's other data. This supplies a concrete decoder
and scan skeleton, while leaving the source readiness/parser, scalar/circle
samplers and message locality to be identified. Only eight block indices
are filtered/minimized, never the commitment position universe.

9018 fails because `prefix` is a Lean keyword; 9019 passes after renaming;
9020 adds and verifies the wire-data constructor and its decoder/scan
properties (1.91s, 3518856 KiB, zero swap, nine standard-axiom audits).

## Final source handoff and stopped target

`PhaseRefinementObstructionBin.prematureC2_excluded` proves that the existing
D85 wire cannot be wrapped in `R1PhaseWire`, even independently of ord.
It instantiates the frame-locality field at row zero and equal challenge
vectors, but different C2 arguments; equality would force byte 0 = byte 1.
Attempt 9017: exit 0, 2.30s, 3516400 KiB, zero swap, standard axioms. Thus the
false target "every existing wire admits the new phase refinement" is
stopped with a compiled counterexample, rather than assumed as a source
identification. No universal conversion is installed.

Exactly what remains before this is the shipped protocol's causal proof:

1. **Message encoding from the honest view.** Define the actual function
   selecting and serializing the semantic round coefficients, claims, OOD
   values and opening messages from `JointView.view`. Prove its frame,
   payload and final dependencies. Include root placement and show that
   arbitrary auxiliary `outputs x ch` cannot affect earlier message bytes.
   The static length carrier supplies none of these equations. In particular,
   the semantic round-polynomial prefix lemma and R1 batched round/final
   message prefix lemmas are not proved here.
2. **Sampler/parser identity.** Identify scalar and circle parameters with
   the shipped block samplers, and the prefix scan readiness and decoder with
   its word parsing, first-22-distinct policy and exhaustion endpoint. The
   constructed scan's prefix property does not establish those identities,
   uniformity, or the query-word history coupling.
3. **Leaf encoding identity.** Instantiate the three encoder parameters with
   S2 transport, domain evaluation, source lane selection and serialization,
   and folded padding. The dependency proof already holds for every such
   encoder. Equality with the shipped C1/C2/folded tree leaves is still needed.
   The canonical builder can specialize the generic honest-prover argument,
   but the D83 builder relation alone supplies no byte encoders.
4. **Execution refinement.** Map source hash calls to positions and normalize
   their order with address/answer preservation. Our independent salts all
   precede C1; the Rust folded salts occur after row 29. Within-stage ties
   are abstract. Actual early-stopping query scans may need unused-block
   normalization. A raw chronological trace is therefore not simply equal
   to the mathematical total order. This is the prospective role of
   `R10_RWire_executes_phase_order`, after (1)–(3), with permitted commutations
   and padding precisely specified. No such hypothesis or proof is installed.

The source inventory JSON pins the read-only inspected files. It is not
source-refinement evidence. Concurrent-worker-owned files are untouched.

The endpoint is **not** restated over an uncertified replacement protocol.
No new premise is advertised as its sole remaining source premise.
`PrivacyR1Final.lean` before/after are byte-identical; its causal premise,
verbatim in both versions, is:

```lean
    (R_causal_D80 : ∀ (w : h.Instance) sec d p v v', Earlier W Pr p v v' →
      attAddr W Pr h B outputs x w sec d v p = attAddr W Pr h B outputs x w sec d v' p)
```

For an actually identified `R1PhaseWire`/`R1PhaseProver`, the new
`PhaseCausalityBin.R_causal_D80` supplies this exact premise as a theorem.
That is the completed mathematical bridge; (1)–(4) are the precise open
source/model joins. In particular, the requested proof that the shipped
encoding inhabits the phase structure has **not** been completed.

## Final verification scope

Eight new Lean modules, 31 new theorems; every theorem has a printed axioms
audit. All current source hashes match a successful focused env-J attempt;
all accepted audits use only subsets of propext/Classical.choice/Quot.sound.
Failed diagnostics (including elaborator-generated sorryAx) are retained
as failed evidence, never counted as accepted theorem results. No forbidden
constructs or additional heartbeat/recursion settings occur in the sources.
Only assigned attempts 9000–9020 were used. All ran under run-joint.sh,
7000 MB / MemoryHigh=5G / MemoryMax=7G / MemorySwapMax=0; the recorded populated
reservation was 24 GiB plus this job's 7 GiB, below 55 GiB. No pre-existing
shared module was overwritten. No frozen-manifest or runtime suite was run:
this is an additive partial causal-model result, not a final privacy release.

| Current target | Attempt | Exit | Wall | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|---:|
| PhaseScheduleBin | 9000 | 0 | 3.27s | 3503544 | 0 |
| PhaseLocalityBin | 9006 | 0 | 2.37s | 3527080 | 0 |
| PhaseTranscriptBin | 9007 | 0 | 3.63s | 3530696 | 0 |
| PhaseCausalityBin | 9009 | 0 | 3.47s | 3519168 | 0 |
| PhaseBuilderDependenciesBin | 9015 | 0 | 2.83s | 3517212 | 0 |
| PhaseLeafConstructionBin | 9016 | 0 | 2.25s | 3522156 | 0 |
| PhaseRefinementObstructionBin | 9017 | 0 | 2.30s | 3516400 | 0 |
| PhaseQueryScanBin | 9020 | 0 | 1.91s | 3518856 | 0 |
