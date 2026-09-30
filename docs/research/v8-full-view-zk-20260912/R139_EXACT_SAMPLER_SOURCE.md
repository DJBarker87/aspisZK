# R139: exact R137 sampler source bridge

Source base: `e31dde36194d03e98da386264b5f655e39edc73b`.

R139 closes the exact R137 QM31 sampler's deterministic source execution:

- wrapping `usize` multiplication/addition equal the checked word-reader
  arithmetic on the source cursor invariant;
- the duplicate source index calculation, four-byte slice, retry decision and
  rollover step match the checked reader;
- the eight-attempt limb loop and four-limb mutable write-back are exact;
- the complete extracted `challenge_qm31` result and advanced transcript state
  equal the existing source-shaped `QM31SamplerProgram.challengeRun` model;
- the extracted three-attempt `challenge_nonzero_qm31` loop unfolds exactly to
  a finite source recurrence.

Every changed Lean leaf compiled in the pinned NUC cache with a 5/7 GiB
high/max cgroup, zero swap and `-j1 -M4500`.  The release bridge has no
`sorryAx`; its printed axioms are `propext`, `Classical.choice`, `Quot.sound`
and the extracted formatter axiom already present in the generated slice
conversion path.

The first remaining proposition is the value/state correspondence between the
finite nonzero recurrence and `SamplerWrapperPolicies.nonzeroRun`, including
the exact encoded-QM31 zero test.  After that, the source callback chronology
must instantiate the selected prefix program.  Oracle admissibility, privacy
and soundness remain open.  The verifier source and measured endpoint are
unchanged at **999,790 / 999,532 CU**.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r139_evidence.py
```
