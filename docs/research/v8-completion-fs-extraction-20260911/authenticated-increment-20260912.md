# Authenticated same-body increment — 2026-09-12

`lean/SameBodyAuthenticatedIncrement.lean` constructs the selected shifted
q22 query increment from the existing same-body wire, packed-record,
inverse/geometry and Merkle-opening pipeline.  A successful `Prepared` value
contains that pipeline's own success equation; opening equality is not a
premise.  Pipeline `none` remains a named aggregate failure, while the
existing `run_checks` theorem exposes the four internal successful checks.

The scalar is exactly

`sum i, rho^(i+1) * opened[i]`,

and its application through the function shape expected by
`SameBodyRelation.consume` is proved equal at the same final, schedule and
rho.  The leaf also constructs the exact canonical 16-byte encoding absorbed
by the later transcript.  Against chronological C1/C2 prefix and log
premises, it proves the existing explicit authentication-failure alternative
or equality with the prefix-bound virtual quotient's actual folded values.

This does not yet install the producer in the live script.  The typed q22
schedule must first be constructed from the same live sampler result, and the
chronological prefixes/log-inclusion premises still need their source
producer.  Literal Rust refinement remains open.

## Focused evidence

- Base revision: `8064af134afb1b2d39ee993cc0c2bcab8d252feb`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Capped NUC compile: `MemoryHigh=8G`, `MemoryMax=9G`,
  `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 3.02 seconds
- Peak RSS: 6,687,140 KiB
- Swap: 0
- Source SHA-256:
  `6551b39898b4b598164468d13af821ad4bbe50af4ac2db585f40b26c4f2aa0d6`
- Olean SHA-256:
  `a5a042b14703bcffda3b16c7d426369191c3843665decdc5f1b7ccaf2234ca84`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

A missing cached V7 dependency was rebuilt from its pinned source before the
final leaf check.  This remains focused evidence, not a clean full-closure
replay.
