import PCC_BasicReferences
import PCC_ReferenceInvariant
set_option autoImplicit false
namespace PCC
open PCA

theorem token_frame (a : Nat) (s : PCA_State) :
    (tokenProgramReference a s).state = s ∧ (tokenProgramReference a s).events = [] := ⟨rfl,rfl⟩
theorem payer_frame (args : Nat × Nat) (s : PCA_State) :
    (payerSystemReference args s).state = s ∧ (payerSystemReference args s).events = [] := ⟨rfl,rfl⟩
theorem unique_frame (s : PCA_State) :
    (uniqueReference () s).state = s ∧ (uniqueReference () s).events = [] := ⟨rfl,rfl⟩
theorem count_preserves (n : Nat) : Preserves (countReference n) := fun _ h => h
theorem token_preserves (a : Nat) : Preserves (tokenProgramReference a) := fun _ h => h
theorem payer_preserves (args : Nat × Nat) : Preserves (payerSystemReference args) := fun _ h => h
theorem unique_preserves : Preserves (uniqueReference ()) := fun _ h => h
#print axioms token_frame
#print axioms payer_frame
#print axioms unique_frame
#print axioms count_preserves
#print axioms token_preserves
#print axioms payer_preserves
#print axioms unique_preserves
end PCC
