# R137 evidence report

- Charon: exit 0, 10.60 s, peak RSS 611,852 KiB, swap 0.
- Aeneas: exit 0, 1.00 s, peak RSS 102,984 KiB, swap 0.
- Six focused Lean targets: exit 0, 1.04--1.73 s each, peak RSS
  2,520,440--2,554,852 KiB, swap 0.
- `to_from_qm31` and `from_to_qm31`: no axioms.
- Raw R137 generated overlay: zero external axioms.
- R136 former external layer: fully implemented and compiled.
- Exact callback-to-program execution bridge: open.
- Actual sampler admissibility, privacy and soundness: open.

The failed attempt to normalize the entire generic packed-absorb implementation
was not retained as a proof result.  The next bridge must factor the framing
and slice-update identities into small symbolic lemmas before compiling the
generated execution theorem.
