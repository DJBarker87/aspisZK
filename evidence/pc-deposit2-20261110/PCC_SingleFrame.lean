import PCC_SingleOutputReference
import PCC_LaneReference
import PCC_ReferenceInvariant
set_option autoImplicit false
namespace PCC
open PCA

theorem single_frame (c : Digest) (s : PCA_State) :
    (singleOutputReference c s).state = s ∧ (singleOutputReference c s).events = [] := ⟨rfl,rfl⟩
theorem single_preserves (c : Digest) : Preserves (singleOutputReference c) := fun _ h => h

theorem lane_frame (c : Digest) (s : PCA_State) :
    (laneReference c s).state = s ∧ (laneReference c s).events = [] := ⟨rfl,rfl⟩
theorem lane_preserves (c : Digest) : Preserves (laneReference c) := fun _ h => h
#print axioms single_frame
#print axioms single_preserves
#print axioms lane_frame
#print axioms lane_preserves
end PCC
