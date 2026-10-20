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
