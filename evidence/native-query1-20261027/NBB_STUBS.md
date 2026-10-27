# NBB replacement table

No field multiplication is executed in any NBB native gate. No field-operation
replacement has been introduced. The inherited multiplication table remains
[evidence/leaf-p6-8-20261027/LPh_STUBS.md](../leaf-p6-8-20261027/LPh_STUBS.md).

| Replacement | Named Lean discharge | Exact domain and status |
|---|---|---|
| NBB_add_reply replacing the factored integer NBB_add | NBB_Arithmetic.add; S7OwnedP6ScalarProof.scalar_success | Arbitrary U64 raw; U32 limb,basis canonical <P; raw<2^34+(terms mod4)*(P-1)^2. Caller overflow follows from phase_bound. This is an integer add/product fragment, not a modular field-operation stub. |
| NBB_fold_reply replacing NBB_fold | NBB_Arithmetic.fold | Every U64 value. Exact natural bit-fold, no canonical or phase premise. |
| NBB_row_reply replacing update_residue_row | NBB_RowTrace.native_result and NBB_RowWitness.construct, composed with K002/K003 and source association; NBB_Row.source provides totality | Four actual U64 limbs, four canonical power U32s, canonical basis, each input row word in SAME terms phase. Selected-reference K004 accepts arbitrary rows/powers/basis/terms and overapproximates this domain. |

These replacements havoc their output and record their actual inputs. They
prove caller routing/frame properties for ALL replies; they are not themselves
natural-value equivalence proofs. The paired Lean scalar/row theorems provide
the unique actual values on the above domains. No kani::assume grants the caller
canonicality. Whole query caller establishment is still OPEN; no full query pass
is credited from the row gates. K001 timed out and is excluded.

The table deliberately does not invent an exact whole-query callee law.
Native arithmetic source association and full caller-domain establishment are
separate gates. No replacement stands for a whole accepted transaction, digest
history, public statement, or headline conclusion.
