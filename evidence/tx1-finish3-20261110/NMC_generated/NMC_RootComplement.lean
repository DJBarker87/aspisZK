import NLU_Nested
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Root
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Total try_into/unwrap suffix on the actual current payload, with no
first-proof persistence or child-success premise. -/
def copy (payload : Slice U8) : Result (Array U8 32#usize) := do
 let attempted ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload
 S1SemanticRootCopy.unwrapRoot attempted
/-- The complementary unwrap-abort law. No buffer or owner post is invented. -/
theorem wrong_length (payload : Slice U8) (bad : payload.length ≠ 32) :
 copy payload=fail .panic := by
 simp only [copy,core.array.TryFromArrayCopySlice.try_from]
 simp only [show ¬ payload.length=(32#usize).val from bad,dif_neg,bind_tc_ok]
 rfl
/-- On exact extent the array contains precisely every current input byte. -/
theorem exact_length (payload : Slice U8) (size : payload.length=32) :
 ∃ root,copy payload=ok root ∧ root.val=payload.val := by
 unfold copy
 simp only [core.array.TryFromArrayCopySlice.try_from]
 simp only [show payload.length=(32#usize).val from size,dif_pos,bind_tc_ok]
 exact ⟨_,rfl,rfl⟩
#print axioms wrong_length
#print axioms exact_length
set_option pp.proofs false in #print wrong_length
set_option pp.proofs false in #print exact_length
end AspisR1.NMC_Root
end
