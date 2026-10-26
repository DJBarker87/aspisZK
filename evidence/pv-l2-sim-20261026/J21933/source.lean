import R1Z.PV_L2_RecordCompact
set_option autoImplicit false
namespace R1Z.PV_L2_RecordRefinement
open Aeneas Aeneas.Std Result R1Z.PV_L2_Record

/-- Named result boundaries keep complete event computations out of kernel
conversion when joining separately proved source operations. -/
theorem bind_erases {α β : Type} (a : Recorded α) (b : Result α)
    (f : α → Recorded β) (g : α → Result β)
    (head : a.value = b) (tail : ∀ x, (f x).value = g x) :
    (PV_L2_RecordCompact.bind a f).value = (do let x ← b; g x) := by
  change (do let x ← a.value; (f x).value) = _
  rw [head]
  exact congrArg (fun h : α → Result β => Bind.bind b h) (funext tail)

#print axioms bind_erases
end R1Z.PV_L2_RecordRefinement
