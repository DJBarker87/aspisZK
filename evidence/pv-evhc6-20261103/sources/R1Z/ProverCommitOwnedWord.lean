import R1Z.ProverCommitOwnedDecoder
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R1Z.ProverCommitWordCarrier
attribute [local instance] Classical.propDecidable

def wordFin (word : U32) : R1Z.CommitReadsR1.Word :=
  ⟨word.val, by simpa only [UScalar.size_def, UScalarTy.U32_numBits_eq] using word.hSize⟩

theorem masked_val (word : U32) :
    (word &&& 2147483647#u32).val = word.val % 2^31 := by
  rw [UScalar.val_and]
  change word.val &&& (2^31-1) = word.val % 2^31
  exact Nat.and_two_pow_sub_one_eq_mod word.val 31

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- The extracted masking, comparison and field conversion implement exactly
the accepted-word predicate used by the fibre model, for every machine word. -/
theorem accepted_word (word : U32) :
    accepted (K := K) (wordFin word) =
      if word &&& 2147483647#u32 < aspis_core.field.P then
        some (fieldValue (word &&& 2147483647#u32)) else none := by
  have comparison : (word &&& 2147483647#u32 < aspis_core.field.P) ↔
      word.val % 2^31 < AspisCircleGroupOrder.P := by
    simp only [UScalar.lt_equiv, masked_val, aspis_core.field.P]
    rfl
  by_cases accepted : word.val % 2^31 < AspisCircleGroupOrder.P
  · rw [if_pos (comparison.mpr accepted)]
    simp only [R1Z.ProverCommitWordCarrier.accepted, wordFin, dif_pos accepted,
      fieldValue, masked_val, Nat.mod_eq_of_lt accepted]
  · rw [if_neg (fun h => accepted (comparison.mp h))]
    simp only [R1Z.ProverCommitWordCarrier.accepted, wordFin, dif_neg accepted]

#print axioms masked_val
#print axioms accepted_word
end R1Z.ProverCommitOwnedDecoder
