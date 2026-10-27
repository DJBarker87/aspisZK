# A3 actual-cohort M31 bridge

L095 proves XRt_CohortMultiply.multiply on ALL raw U32 x,y, with complete Result equality:

```lean
XRn_Join_Field.field.M31.mul x y =
 AspisR1Qm31ArithmeticProbe.field.M31.mul x y
```

Before: only XRn=FIo and semantic-extraction base multiplication were checked (XRs_BaseMultiply); actual cohort probe multiplication was open. After: equality above is unconditional. XRt_CohortMultiply.canonical_output additionally produces the SAME z returned by both calls, its exact residue (x.val*y.val)%2147483647 and z.val<2147483647, also without input canonicality or success premise. It composes the inherited XRs and current-reducer value theorems and scalar extensionality; no multiplication/reduction fact is reproved.

L095 co-imports every new checked XRt query proof plus the inherited XRs/LPk/LPf/LPh closure. Both new theorems print only propext/Classical.choice/Quot.sound. Exit0, wall2.117845725s, RSS4762724KiB, swap0, exact source revision/hash/dependencies and limits in receipt.

A3 remains OPEN: CM31 and QM31 multiplication, mul_u, canonical outputs to installed claim arithmetic, SAME powersPublic29, six selections, seven weighted parts and every error/effect. prepared_claim P6 remains OPEN; no merged LPm closure appears in inspected research revision2b4e9c88de829a2898c876fc13b5aacf47d099b9. Remaining budget imports the already checked LPi field chain verbatim, without new credit.

Actual headline statement and ledger unchanged: removed0, added0, changed0; deltaT0/P0/G0/C0,83T/0P/13G with L154 parameter. The existential canonical-output theorem for arbitrary inhabited U32 inputs is explicit local operation non-vacuity; no joint deployed accepted-root witness is supplied. No shipped/cfg(kani)/Rust source changed and no artifact rebuild was triggered.
