import PCC_InfosReference
set_option autoImplicit false
namespace PCC
open PCA

theorem infos_frame (accounts : List Nat) (s : PCA_State) :
    (infosReference accounts s).state = s ∧ (infosReference accounts s).events = [] := by
  unfold infosReference
  split
  · dsimp only
    split <;> exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

theorem infos_order (mint source authority vault token : Nat) (s : PCA_State)
    (unique : ([mint,source,authority,vault,token].map
      (fun a => (s.loans.state.accounts a).key)).Pairwise (· ≠ ·)) :
    (infosReference [mint,source,authority,vault,token] s).reply =
      .ok ⟨#[source,mint,vault,authority,token],rfl⟩ := by
  simp only [infosReference,if_pos unique]
#print axioms infos_frame
#print axioms infos_order
end PCC
