# Phase 2 protocol joins

Branch `codex/cx-priv-phase2-20261021`, base `cc4eaf763`.
Only new modules and supporting evidence are added. No concurrent-worker-owned
source is edited. Compiles use env J, attempts 9400–9599, the existing capped
launcher, and a branch-specific runner derived from run-phase-attempt.py.

## Stage 1: endpoint inspection and compiled obstruction

The actual final privacy theorem does not fix a message encoder. In
`PrivacyR1Final.lean`, its local notation is verbatim:

```lean
local notation "W" => RomFiniteBin.wire base (RomGrammarBin.bound publicWidth)
```

`base` is universally quantified. `RomFiniteBin.wire` retains frame, payload,
final, decoder, kstarOf, and comLog unchanged; only the table backend and query
cap are replaced. Consequently the D85 premature-C2 witness remains admitted
at exactly this endpoint. `PhaseEndpointObstructionBin` proves that this
endpoint instance cannot inhabit `R1PhaseWire` and that a universal endpoint
refinement is impossible. This is a compiled counterexample to the requested
ideal endpoint conversion, not a proof that the shipped Rust protocol fails.
A new concrete encoder can be useful independently, but it is not definitionally
the arbitrary endpoint `base`.

Attempt 9400: exit 0, 1.99s wall, 3512252 KiB peak RSS, zero swaps. Both
printed axioms audits contain only propext, Classical.choice, Quot.sound.
Full source SHA, dependency object fingerprints, revision, launcher reservation,
output, and timing are in `phase2-attempts-9400-9599.jsonl`.

`PrivacyR1Final.lean` is unchanged. Its causal premise before and after is
verbatim:

```lean
    (R_causal_D80 : ∀ (w : h.Instance) sec d p v v', Earlier W Pr p v v' →
      attAddr W Pr h B outputs x w sec d v p = attAddr W Pr h B outputs x w sec d v' p)
```

No execution-refinement-only replacement is justified at this endpoint.
Independent model joins follow below.

## Stage 2: semantic and batched message prefixes

`PhaseMessageDependenciesBin` proves roundPoint and the semantic polynomial
and actual semantic coefficient cells depend only on semantic rows strictly
before 15+j. It proves R1 round0 depends on semantic/circle values, gamma and
kappa; round1 additionally uses alpha0; final uses gamma, alpha0 and alpha1
and needs neither kappa nor circle/query answers. These are symbolic facts
about the existing HonestView/Batched maps, not replacement polynomials.

9401 and 9402 retain failed elaboration diagnostics (finite-index arithmetic,
then simplification under the weights vector). 9403 passes all nine audits:
exit 0, 2.27s, 3522128 KiB, zero swaps, only the standard three axioms.
Replacing this branch's new shared module snapshots its source/object under
`aspis-joint-20261019/snapshots/codex-cx-priv-phase2-20261021/<attempt>`;
no pre-existing shared module is replaced.

## Stage 3: logical message encoder and phase inhabitant

`PhaseMessageEncodingBin` selects the actual cells of JointView.view: maskSum,
ten semantic coefficient vectors, three point-claim vectors plus extra claims,
OOD0/1, inactive claim, R1 round0/1, final64. C2 is supplied only at row2;
the folded root only at row30. The arbitrary metadata/Aux output is never
passed to the encoder. `auxiliary_irrelevant` proves this for the entire
encoded transcript, not just its early bytes. Frame/payload/final locality
and `phaseWire` compile. `wideBytes` reuses FoldedLeafCodec.encodeWide;
`encoded` reuses FixedWidthDecoder.encode; `framed` reuses RecordFrameCodec.
The abstract field-encoder version permits reusable dependency proofs;
wideBytes is the explicit exact-wide specialization, not a new field codec.

The existing codec objects were missing in env J. Attempts 9405–9417 compile
13 unchanged existing source modules, individually in dependency order, with
full evidence and original source paths. Their sources were not edited or
added to the branch. They were absent from the shared objects tree; any
existing shared sources/objects were snapshotted by the runner before upload.
The runner now resolves imports using the actual env-J object search paths
and can read unchanged spend-path dependencies. The initial 9404 preflight
failed on a missing object before invoking the launcher (no compile occurred).

9418 exposed broad congruence trying to unfold finite encodings. Replaced it
with explicit congrArg applications and kept encoded/framed locally opaque;
no resource settings were raised. 9419 passes all 11 new audits: exit 0,
3.60s, 3542044 KiB, zero swaps, standard axioms only. The other failed
diagnostics remain in the evidence and are not counted as proof results.

This closes message locality for the constructed model. It supplies no
equality between that model and the final theorem's arbitrary `base`.

## Stage 4: concrete sampler/parser and leaf joins in the Lean model

`PhaseSamplerParserBin` fixes semantic sampling to the extracted spend-path
`s1Spend` through the exact-tower algebraMap, fixes both circle blocks to the
existing total fallback policies, and uses gammaNZ/ordinary for opening
blocks. It supplies SemRows01, its exact s1Spend identity, DecodeLocal and
nonzero gamma. A single shared scalar parameter cannot identify this decoder:
semantic samples are QM31; opening samples are wide, and gamma is nonzero.
The generic DecodeLocal interface supports the required distinct maps.

Query candidates use the existing SamplerWords.words (eight LE u32s, low
18 bits), and the existing Q22WordScan recurrence. Readiness is its actual
Boolean completion signal, not just accepted.length=22. Completion on the
eighth word is detected at the next nonempty block. The model chooses the
first ready block or index7 on exhaustion. Proven: no earlier completion,
parsed prefix ignores zero extension, candidate bounds, selected-prefix
noninterference, and successful decoding equals the stable first 22 distinct
word values. This identifies the Lean parser/policy; no Rust ordered-call or
reached-history law is claimed. A failed finish is not asserted successful;
its partial set is retained only as a total counterfactual decoder value.

`PhaseCircleBlocksBin` isolates the small concrete circle adapter. Attempts
9423/9425/9429/9430 hit elaborator typeclass reduction of the concrete wide
alias; the focused 9427 diagnostic verified the adapter independently. Using
literal type notation in the combined module removes that reduction without
raising heartbeats or recursion limits. Its exact diagnostic source is
retained as `circle-type-probe-9427.lean.txt`. 9433 and 9434 pass the final
adapter/parser sources with standard axioms and zero swaps. Existing unchanged
QueryScanModelFailure/QueryScanOrderedModel dependencies pass 9420/9421.

`PhaseLeafEncodingBin` fixes all three LeafEncoding parameters. It uses
D18/S2's involution, the existing exact initial-circle and folded-line domain
evaluators, slot-major then lane-major ordering, 4-byte lanes 0..25, 16-byte
lane28 and C2 lanes26/27, and the existing exact-wide/folded codecs. Data
folded leaves are below 65536; all remaining leaves are 128 zero bytes.
`extracted_s2_index` consumes BuilderTransport.reference_row_fin. `honest_leaves`
identifies the constructor's three leaves with these model definitions;
`c1_view`, `c2_view`, and `folded_view` identify their queried data with the
actual HonestView.run cells (S2 transport explicit for C1/C2, FoldedOpen
explicit for folded). This does not prove the Rust FFT implementation,
its low-subfield guards, or leaf hash-call execution correspondence.

9422/9424/9428 preserve intermediate diagnostics. 9426 and 9431 pass earlier
subsets; 9435 passes the final 11-audit leaf source. Final parser and leaf
attempts: 9434 = exit0, 2.83s, 4035060 KiB; 9435 = exit0, 3.99s,
4002752 KiB. Both zero swaps and only standard axioms. The branch-specific
runner now freezes the uploaded source digest before launching and exits
nonzero on a Lean failure, after preserving the evidence.
