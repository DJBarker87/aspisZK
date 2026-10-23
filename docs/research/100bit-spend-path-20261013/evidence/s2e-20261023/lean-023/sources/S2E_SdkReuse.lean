import S2E_Model
import S2SdkOwnedModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2E.SdkReuse
open S2E_Reference.S2E_Reference

/-- Literal source-operation reuse after the checked carrier aliases. These
identify two owned mathematical models, not either model with actual SDK guards. -/
theorem shared_allowed_same (counter : Isize) :
    shared_allowed counter = SdkReference.shared_allowed counter := rfl

theorem shared_same (sdk : OwnedSdk) (slot : Usize) :
    owned_acquire_shared sdk slot = SdkReference.owned_acquire_shared sdk slot := rfl

theorem exclusive_same (sdk : OwnedSdk) (guards : LiveGuards) (slot : Usize) :
    owned_acquire_checkpoint sdk guards slot =
      SdkReference.owned_acquire_checkpoint sdk guards slot := rfl

theorem length_same (sdk : OwnedSdk) (slot : Usize) :
    owned_data_len sdk slot = SdkReference.owned_data_len sdk slot := rfl

theorem release_same (sdk : OwnedSdk) (guards : LiveGuards) :
    owned_release_guards sdk guards = SdkReference.owned_release_guards sdk guards := rfl

#print axioms shared_allowed_same
#print axioms shared_same
#print axioms exclusive_same
#print axioms length_same
#print axioms release_same
end AspisR1.S2E.SdkReuse
