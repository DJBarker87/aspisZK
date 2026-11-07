import NNH_ValidateFission
set_option autoImplicit false
namespace NNH_ValidateScanCongr
open Aeneas Aeneas.Std AdapterRw

theorem same (left right : Ops) (h9 : @left.op9=@right.op9)
 (h35 : left.op35=right.op35) (h51 : left.op51=right.op51) (h52 : left.op52=right.op52) :
 NNH_ValidateFission.scan left=NNH_ValidateFission.scan right := by
 cases left
 cases right
 cases h9
 cases h35
 cases h51
 cases h52
 rfl
#print axioms same
end NNH_ValidateScanCongr
