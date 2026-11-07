import NMS_R2Success
import NMS_R2StepFacts
set_option autoImplicit false
namespace NMS_R2Getters
open RSL NMS_R2Refine
/-- A successful getter returns its stored Ok. Clone allocation failures have
no returned value and cannot furnish an entered-path cut. -/
theorem success {A : Type} (stored : Except ProgramError A) (env : Env)
 (value : A) (events : List Event)
 (run : RS.ofCloned stored env ⟨.ret (.ok value),events⟩) : stored = .ok value := by
 cases stored with
 | ok original =>
   have same := Except.ok.inj (NMS_R2Success.pure_return _ _ env events run)
   exact congrArg Except.ok same.symm
 | error e =>
   unfold RS.ofCloned at run
   cases allocation : e.cloneAllocates with
   | true =>
     simp only [allocation, Bool.true_eq, ↓reduceIte] at run
     obtain ⟨_,_,_,_,last,_⟩ := rsbind_return _ _ _ _ _ run
     have impossible := congrArg Obs.exit last
     cases impossible
   | false =>
     simp only [allocation, Bool.false_eq_true, ↓reduceIte] at run
     have impossible := congrArg Obs.exit run
     cases impossible

/-- This fact follows only from a returning checkpoint observation. It does
not exclude any cloned-error abort from the full checkpoint law. -/
theorem checkpoint_success (a : OwnedAccount) (program : B32) (writable : Bool)
 (env : Env) (events : List Event)
 (run : verifierCheckpoint a program writable env ⟨.ret (.ok ()),events⟩) :
 a.length = .ok CHECKPOINT_BYTES := by
 unfold verifierCheckpoint at run
 split at run
 · have impossible := congrArg Obs.exit run
   cases impossible
 · obtain ⟨n,_,_,read,checked,_⟩ := rsbind_return _ _ _ _ _ run
   have stored := success a.length env n _ read
   have guard := NMS_R2StepFacts.check_return _ _ env _ checked
   have same : n = CHECKPOINT_BYTES := by simpa using guard
   exact stored.trans (congrArg Except.ok same)
#print axioms success
#print axioms checkpoint_success
end NMS_R2Getters
