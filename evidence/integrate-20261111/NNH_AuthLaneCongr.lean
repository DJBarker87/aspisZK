import NNH_AuthTailParts
set_option autoImplicit false
noncomputable section
namespace NNH_AuthLaneCongr
open Aeneas Aeneas.Std AdapterRw

theorem same (left right : Ops)
 (h35 : left.op35=right.op35)
 (h36 : left.op36=right.op36)
 (h38 : left.op38=right.op38)
 (h39 : left.op39=right.op39)
 (h40 : left.op40=right.op40)
 (h50 : left.op50=right.op50)
 : NNH_AuthTailParts.lane left=NNH_AuthTailParts.lane right := by
 cases left
 cases right
 cases h35
 cases h36
 cases h38
 cases h39
 cases h40
 cases h50
 rfl
#print axioms same
end NNH_AuthLaneCongr
