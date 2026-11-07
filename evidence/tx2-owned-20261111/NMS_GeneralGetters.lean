import NMS_CloneReference
import NMS_RSLStepFacts
set_option autoImplicit false
namespace NMS_GeneralGetters
open RSL NMS_RSLSuccess

def get {A : Type} (stored : Except ProgramError A) : RS A :=
 match stored with
 | .ok value => RS.pure value
 | .error error => Spec.bind (NMS_CloneReference.clone error) (fun reply => RS.throw reply)

def data (a : OwnedAccount) : RS Bytes := get a.bytes
def length (a : OwnedAccount) : RS Nat := get a.length

theorem data_eq (a : OwnedAccount) : data a = NMS_CloneReference.data a := by
 unfold data get NMS_CloneReference.data
 cases a.bytes <;> rfl

theorem success {A : Type} (stored : Except ProgramError A) (env : Env) (value : A)
 (events : List Event) (run : get stored env ⟨.ret (.ok value),events⟩) : stored = .ok value := by
 cases stored with
 | ok original =>
   have same := Except.ok.inj (pure_return _ _ env events run)
   exact congrArg Except.ok same.symm
 | error error =>
   obtain ⟨_,_,_,_,last,_⟩ := bind_return _ _ _ _ _ run
   have impossible := pure_return _ _ _ _ last
   cases impossible

/-- Source-order checkpoint guard, now including the stopped cloned-length
arm at the actual data_len call. Normal values/errors are unchanged. -/
def checkpoint (a : OwnedAccount) (program : B32) (writable : Bool) : RS Unit :=
 RS.seq (RS.check (decide (a.owner ≠ program) || a.is_signer || a.executable || a.is_writable != writable)
   .invalidAccountData) <|
 RS.bind (length a) fun n => RS.check (n != CHECKPOINT_BYTES) .invalidAccountData

theorem checkpoint_success (a : OwnedAccount) (program : B32) (writable : Bool)
 (env : Env) (events : List Event) (run : checkpoint a program writable env ⟨.ret (.ok ()),events⟩) :
 a.length = .ok CHECKPOINT_BYTES := by
 unfold checkpoint at run
 obtain ⟨_,_,_,_,run,_⟩ := NMS_RSLRefine.rsbind_return _ _ _ _ _ run
 obtain ⟨n,_,_,read,checked,_⟩ := NMS_RSLRefine.rsbind_return _ _ _ _ _ run
 have stored := success a.length env n _ read
 have guard := NMS_RSLStepFacts.check_return _ _ env _ checked
 have same : n = CHECKPOINT_BYTES := by simpa using guard
 exact stored.trans (congrArg Except.ok same)

#print axioms data_eq
#print axioms success
#print axioms checkpoint_success
end NMS_GeneralGetters
