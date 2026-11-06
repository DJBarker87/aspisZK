import NJT_ClaimsRef_Funs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_ClaimsRef_Code
open Aeneas Aeneas.Std Result
open AspisR1ClaimsUnrolledParent

def singleton (value : Claims) : Slice Claims := ⟨[value], by simp⟩

theorem filled_one (value : Claims) :
 NJT_ClaimsRef.aspis_core.r0.heap.filled
  (Array.Insts.CoreMarkerCopy 3#usize (Array.Insts.CoreMarkerCopy 29#usize
    NJT_ClaimsRef.aspis_core.field.QM31.Insts.CoreMarkerCopy)) 1#usize value =
 ok (.Ok (singleton value)) := by
 rfl

#print axioms filled_one
end AspisR1.NJT_ClaimsRef_Code
end
