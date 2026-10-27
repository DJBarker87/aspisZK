import R1Z.PV_RunJoin_AbsorbShape20
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodeShape20
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem pre (right : Array U32 8#usize) (target : Array U32 16#usize)
    (hr : Canon8 right)
    (h : ∀ j, j < 16 → (target.val[j]!).val = if j < 8 then 0 else if j = 15 then
      (if 2147483647 ≤ (right.val[7]!).val + 1095962629 then (right.val[7]!).val + 1095962629 - 2147483647
       else (right.val[7]!).val + 1095962629)
      else if j < 16 then (right.val[j-8]!).val else 0) :
    R0BlockCopies.node_pre right = ok target := by
  obtain ⟨p,hp,hv⟩ := node_pre_spec right hr
  have he : p = target := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    apply UScalar.eq_of_val_eq
    exact (hv j).trans (h j (by simpa using hj)).symm
  exact hp.trans (congrArg Result.ok he)
#print axioms pre

theorem absorb (left : Array U32 8#usize) (target : Array U32 16#usize)
    (h : ∀ j, j < 16 → (if j < 8 then left.val[j]! else 0#u32) = target.val[j]!) :
    R0BlockCopies.node_absorb left = ok target := by
  obtain ⟨a,ha,hv⟩ := node_absorb_spec left
  have he : a = target := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    exact (hv j).trans (h j (by simpa using hj))
  exact ha.trans (congrArg Result.ok he)
#print axioms absorb
end R1Z.PV_RunJoin_NodeShape20
