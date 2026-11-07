import NNH_AuthCheckpointCongr
set_option autoImplicit false
noncomputable section
namespace NNH_AuthMasterCongr
open Aeneas Aeneas.Std AdapterRw

theorem same (left right : Ops)
 (h16 : left.op16=right.op16) (h35 : left.op35=right.op35) (h36 : left.op36=right.op36)
 (h37 : left.op37=right.op37) (h38 : left.op38=right.op38) (h39 : left.op39=right.op39)
 (h40 : left.op40=right.op40) (h48 : left.op48=right.op48)
 (child : NNH_AuthTailParts.checkpoint left=NNH_AuthTailParts.checkpoint right)
 (registry : r1_pool_adapter.owned.authenticate_invariant_release_registry left=
  r1_pool_adapter.owned.authenticate_invariant_release_registry right) :
 NNH_AuthTailParts.master left=NNH_AuthTailParts.master right := by
 unfold NNH_AuthTailParts.master
 rw [child,registry]
 cases left
 cases right
 cases h16
 cases h35
 cases h36
 cases h37
 cases h38
 cases h39
 cases h40
 cases h48
 rfl
#print axioms same
end NNH_AuthMasterCongr
