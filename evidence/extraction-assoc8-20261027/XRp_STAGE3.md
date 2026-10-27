# Stage 3: exact A2 sampler equation refuted

XRp_LowSamplerObstruction.all_blocks_law_false (L089, exit0) refutes the EXACT
first law required this round:

```
∀ block, XRn_Join_Release.sampler.low_base_p_digits block =
  AspisR1Post25Sampler.sampler.low_base_p_digits block
```

Concrete block is `ff ff ff 7f` followed by 28 zero bytes (little-endian P).
The emitted full Result is `ok (replicate 8 0, 2147483647)`, proved by
`emitted_low`, composing eight checked word callbacks, the actual library
from_fn, eight stateful closure calls and the actual final array index.
`candidate_bound` imports the existing checked `low_candidate_refines` and
`rank_div_P8_le_256` results; it proves every successful candidate quotient is
≤256. It does not re-evaluate a 256-bit recurrence or re-prove that mathematics.
Thus the two complete Results differ. Both the all-input law and its concrete
instance are refuted. The proof has NO caller success/refinement hypothesis.

This is a selected emitted/cohort-model counterexample, not a shipped Rust
bug claim. The frozen Rust has `*limb = (dividend / P) as u32`; the selected
emitted loop discards the quotient and its restoration reconstructs length16,
so Array.from_slice keeps the old length8 rank. Native/ELF pins were not changed.
No fabricated emitted loop, alternative B, new trust or cohort weakening.

A2 stays OPEN, now with a FALSE first sampler commutation obligation. Stop its
dependent ordinary/gamma and whole scratch composition until the selected
emission/adapter/cohort association is legitimately repaired. A1 inherits this
operation-association obstruction. A0,A3,A4,A5,A6,A7,A8 individually remain OPEN.
All five changed interfaces remain OPEN; FJv_Top statement and 83T/3P/13G ledger
unchanged (deltaT0/P0/G0/C0). No accepted joint root inhabitant is produced.
Local non-vacuity: literal emitted success plus unconditional candidate quotient
bound; earlier division success/success witness and rejected initialization
remain checked. Existing candidate totality is available through the imported
low_base_p_digits_success theorem; no vacuous success assumption is used.

A3 independent work: U32 checked/wrapping add/sub on no-overflow domains (L084)
and canonical M31 addition operation equality (L090). Direct arbitrary QM31
transport L070 was rejected. L091 attempted scalar-sub composition is rejected
for recursion/kernel memory; see XRp_MEMORY_REPLACEMENT.md for the split.
Whole powersPublic, six selections/seven weighted parts and prepared_claim P6
remain OPEN. Research was inspected read-only; no merged LPf certificate found.
