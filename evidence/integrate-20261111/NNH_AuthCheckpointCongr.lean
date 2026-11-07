import NNH_AuthTailParts
set_option autoImplicit false
noncomputable section
namespace NNH_AuthCheckpointCongr
open Aeneas Aeneas.Std AdapterRw

theorem same (left right : Ops)
 (h35 : left.op35=right.op35)
 (h36 : left.op36=right.op36)
 (h38 : left.op38=right.op38)
 (h39 : left.op39=right.op39)
 (h40 : left.op40=right.op40)
 (h49 : left.op49=right.op49)
 (child : NNH_AuthTailParts.lane left=NNH_AuthTailParts.lane right)
 : NNH_AuthTailParts.checkpoint left=NNH_AuthTailParts.checkpoint right := by
 unfold NNH_AuthTailParts.checkpoint
 rw [child]
 cases left
 cases right
 cases h35
 cases h36
 cases h38
 cases h39
 cases h40
 cases h49
 rfl
#print axioms same
end NNH_AuthCheckpointCongr
