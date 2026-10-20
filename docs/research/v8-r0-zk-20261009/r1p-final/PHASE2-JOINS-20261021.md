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

## Stage 5: composed instance, endpoint specialization, final audit

`PhaseProtocolInstanceBin` composes the exact-wide message encoder, concrete
sampler/parser and S2 leaves into R1PhaseWire/R1PhaseProver. Residual tape
coins/counters/opening data remain supplied by the existing prover-data type;
leaf values, commitment grammar and phase order are constructed.
`causal_premise` proves the exact universally quantified D80 condition for
this composed model, without an execution-order premise, even on inconsistent
answer vectors. `rows01`/`sampler_source` provide its sampler handoff.

`baseWire` is the concrete message/decoder model to pass to the existing
final theorem. `endpoint_wire` proves its phase wire is definitionally the
same wire as `RomFiniteBin.wire (baseWire base) (RomGrammarBin.bound publicWidth)`.
Thus there is a usable endpoint **specialization** for an explicitly selected
base, not a universal conversion of the endpoint's still-arbitrary base.
The original theorem is not silently rebound to this specialization.

9436/9437/9439/9440 preserve failed dependent-parameter/section-notation
elaboration diagnostics. 9441 passes the final composition: exit0, 5.55s,
4042732 KiB, zero swaps, seven standard-axiom audits. The endpoint obstruction
is strengthened with the direct noncausality corollary at the ROM-wrapped
D85 witness (with its original late-C2 order condition); 9438 passes:
exit0, 1.92s, 3513924 KiB, zero swaps, three standard-axiom audits.

`audit-phase2-evidence.py` verifies all seven current source hashes have a
successful focused compile, every new theorem has an axioms print, all 57
final prints use only propext/Classical.choice/Quot.sound, no forbidden proof
constructs/options occur, all attempt IDs are assigned, and all swaps are zero.
Its output is `phase2-final-audit.json`. All 41 recorded attempt hashes were
also compared to the launcher's independent sha-<attempt>.txt records; zero
mismatches. 9404 was a dependency preflight only, not a compilation attempt.
The largest recorded peak RSS was below 4.1 million KiB. Every launcher used
7000 MB, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, and reported a populated
reservation of 24 GiB plus the 7 GiB job. No uncapped build, local Lean compile,
Rust gate, package-wide build or repeated unchanged regression was run.
No frozen-manifest release replay is claimed: this is an additive model/source
handoff with an explicitly stopped generic-endpoint target.

## Exact remaining scope

1. At the final theorem's generic base/Pr, no source identification with the
constructed model is present. Its binding must be specialized (or the source
wire/prover identified with the specialization) before consuming causal_premise.
The allowed edit to PrivacyR1Final was only a strictly weaker premise; we made
no such edit because an execution-only replacement is not justified there.
The before/after causal premise quoted in stage1 and the entire file remain
byte-identical (SHA in phase2-final-audit.json).
2. Lean-model samplers, parser, framing, serialization and leaf evaluators are
now explicit. Rust equality, field-guard/rejection behavior, FFT correspondence,
and actual reached-query history coupling remain source joins. The extracted
QM31 sampler and extracted S2 index are reused where already proved; no broader
Rust identity is inferred. Source inventory hashes are read-only evidence.
3. Execution refinement still needs addressed-call/answer preservation under
permitted commutations, salt scheduling and unused query-block normalization.
The mathematical model's causal theorem needs no such execution hypothesis.
4. Existing builder/checker/real/ideal experiment handoffs in the final theorem
remain as before; concurrent-worker-owned files and harnesses are untouched.

No push or merge was performed. All work is confined to this worktree.
