# Derived distinct q22 schedule

This continuation leaves the preceding checked source batch unchanged.

## Checked new result

`FSQuerySchedule.lean` proves:

1. `fuel_stable`: any two block allowances satisfying
   `64 <= draws + 8*fuel` give the same sampler result **and complete state**.
   Thus eight blocks from draw0 suffice. No boundary squeeze is removed.
2. `reference_success`: a successful actual reference run, starting with a
   valid accepted prefix, returns a list of exactly22 distinct indices below
   262144. Empty-prefix validity is proved, not supplied by the caller.
3. `from_success`: produces an injective `Fin22 -> Fin262144` directly from
   those returned list elements. No desired positions or candidate list is
   an input. The list-read identity is `from_success_values`.

The fuel result is a deterministic finite-loop adequacy theorem. It is not
a distribution calculation, independent-draw assumption, or Fiat–Shamir bound.
Source bitwise/integer refinement remains separate.

Focused reproduction:

```sh
python3 docs/research/v8-completion-fs-extraction-20260911/FocusedLeaves.py --root FSQuerySchedule
```

Local Lean4.33.1 Std-only closure PASS at
`results/v8-completion-fs-extraction-20260911/FSQuerySchedule-_xf1_vxx/`.
Changed leaf: exit0; runner0.6126425s; `/usr/bin/time`0.50s,
RSS687325184 bytes, zero swaps. Axioms: only `propext`, `Classical.choice`,
`Quot.sound`; no custom or sorry axiom. Fresh kernel replay NOT RUN.
First failed attempt (`FSQuerySchedule-y3n72p1e`) is retained: symbolic other-fuel
case splitting was needed to expose the capped branch. Statements unchanged.

Checked source SHA256:
`d700c16c0772c585b4b791762bc1fba07f03bf186d581d0b50390912a654dd62`.

## Checked source join

`FSV7SampledBodyScript.lean` combines:

- absorption of the same body's4096 final256 bytes and third eight-byte nonce
  under source labels53 and5;
- the exact block-shaped query sampler;
- the derived typed schedule;
- the already checked same-body Merkle suffix.

Its checked theorem removes the independently supplied query schedule from
this boundary. It still takes an incoming **pre-query transcript**, whose
production through the preceding semantic/OOD/image/row/alpha0 phases remains
an explicit source obligation. It does not move the complete proof body into
a pre-challenge adversarial callback or establish an ideal/ROM coupling.

The join is intentionally not a literal complete query-phase trace.  The
selected research Rust absorbs `AV8/query-batch/v1` and samples nonzero `rho`
after the schedule and before `opened_values` starts the leaf/node hashes
(`relation_callback.rs:122--125,286--288`).  This leaf goes directly from the
schedule to the pure Merkle script.  It therefore proves schedule-to-opening
position coherence, not the intervening transcript/effect order or the final
query-phase oracle state.

The first historical Lean 4.32 integration attempts exposed a proof-dependent
match-elimination incompatibility around `from_success`; the failed v7 run is
retained.  A small generic branch eliminator and definitionally equivalent
research-model refactoring resolved it without adding a premise.  The final
`sampled_body_constructs` theorem passed pinned Lean 4.32 with standard
axioms.  Evidence is in
`results/v8-completion-fs-extraction-20260911/sampled-body-v13/report.json`.
Fresh dependency/kernel checking and actual Rust refinement are NOT RUN.

Next: instantiate its incoming state with the actual compact response0/fold
execution, insert the rho boundary and prove canonical fixed-field
serialization matches the byte ranges it absorbs. No global security or CU
claim follows.
