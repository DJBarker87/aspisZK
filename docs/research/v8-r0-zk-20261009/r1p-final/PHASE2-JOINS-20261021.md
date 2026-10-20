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
