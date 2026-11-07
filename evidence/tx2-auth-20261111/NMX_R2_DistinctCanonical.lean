import NMX_R2_KeyCarrier
set_option autoImplicit false
namespace NMX_R2_DistinctCanonical
open RSL
/-- The canonical scan has the same pairwise condition, including rejection. -/
theorem success (xs : List OwnedAccount) :
 distinctKeys xs = true ↔ xs.Pairwise (fun a b => a.key ≠ b.key) := by
 induction xs with
 | nil => simp [distinctKeys]
 | cons a xs ih =>
   simp only [distinctKeys,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,ih,List.pairwise_cons]
   constructor
   · intro h
     exact ⟨fun b hb same => h.1 b hb same.symm,h.2⟩
   · intro h
     exact ⟨fun b hb same => h.1 b hb same.symm,h.2⟩
#print axioms success
end NMX_R2_DistinctCanonical
