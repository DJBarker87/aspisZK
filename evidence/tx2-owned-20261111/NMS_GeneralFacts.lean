import NMS_GeneralGetters
set_option autoImplicit false
namespace NMS_GeneralFacts
open RSL
/-- Only a normal successful checkpoint guard is projected into the pure
canonical guard; independent cloned-length stops are never projected to Ok. -/
theorem checkpoint_pure_success (a : OwnedAccount) (program : B32) (writable : Bool)
 (env : Env) (events : List Event)
 (run : NMS_GeneralGetters.checkpoint a program writable env ⟨.ret (.ok ()),events⟩) :
 verifierCheckpoint a program writable = .ok () := by
 have length := NMS_GeneralGetters.checkpoint_success a program writable env events run
 unfold NMS_GeneralGetters.checkpoint at run
 obtain ⟨_,_,_,check,_,_⟩ := NMS_RSLRefine.rsbind_return _ _ _ _ _ run
 have metadata := NMS_RSLStepFacts.check_return _ _ env _ check
 unfold verifierCheckpoint
 rw [metadata]
 simp only [Bool.false_eq_true,if_false,OwnedAccount.data_len,length,bne_self_eq_false]
#print axioms checkpoint_pure_success
end NMS_GeneralFacts
