# Proof preparation (unchecked; no extraction gate bypass)

1. Fresh extraction of the three applied bodies with pinned Charon/Aeneas,
   including strict joins and preflight. Source-binding hashes name the actual
   prover-local powers file, not weights.rs. Keep raw outputs verbatim.
2. Check emitted types first, then shift-adapted functions independently.
   Document every positive literal port and the masked usize→U32 cast.
   Prove each port cannot fail and preserves its numeric shift operand.
3. op230: finite-loop equality for arbitrary slice, preserving every Result
   constructor, then ordered fold equality and the 1024/other-length Option
   split. Bridge the value/carrier and original row statement separately.
4. op254: arbitrary-N finite-loop equality (including N=0); bridge the final
   iteration to the original early-return powers loop. The predecessor's
   P6 early-return source is available as a structural reference; a carrier
   map and primitive-result correspondence must be proved before reuse.
5. op258: innermost two-slot loop, two-side loop, then arbitrary-length outer
   scan. Inputs longer than 1024 can hit the 64-word mask bound; preserve
   that Result behavior rather than asserting unconditional successful scan.
   Prove full verdict equality with the original ordered iterator scan,
   including absorbing false while retaining source evaluation/order effects.
6. Every claimed law named PV_B1_<name>.opN_source must cover complete Result
   and arbitrary inputs; finite controls alone do not discharge value laws.
7. Native client and baseline/candidate fixture gate; final source/dependency
   audit. Audit IDs53897–53899 remain reserved. No new trust fields or endpoint
   premise removal can be claimed from draft statements or passing imports.
