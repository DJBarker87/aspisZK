import NKK_RawFold
import NJU_ResumeObserved
set_option autoImplicit false
noncomputable section
namespace NKK_EmbedRaw
open Aeneas Aeneas.Std Result NKK_NativeRaw

/-- The native segment event is embedded in the actual resume Event carrier.
The Reader, full Result and width remain identical. -/
def event {n : Usize} (e : NKK_RawFold.Event n) : NJU_ResumeObserved.Event :=
 .raw n e.before e.reply

def run {E F A : Type} (f : E → F) (m : NJU_Log.Run E A) : NJU_Log.Run F A :=
 ⟨m.result,m.events.map f⟩

theorem result {E F A : Type} (f : E → F) (m : NJU_Log.Run E A) :
 (run f m).result=m.result := rfl

theorem pure {E F A : Type} (f : E → F) (a : A) :
 run f (Pure.pure a : NJU_Log.Run E A)=pure a := rfl

theorem bind {E F A B : Type} (f : E → F) (m : NJU_Log.Run E A)
 (k : A → NJU_Log.Run E B) :
 run f (m >>= k)=((run f m) >>= fun a=>run f (k a)) := by
 cases m with
 | mk result events =>
  cases result with
  | fail err => rfl
  | div => rfl
  | ok a =>
   change (⟨(k a).result,(events++(k a).events).map f⟩ : NJU_Log.Run F B)=_
   rw [List.map_append]
   rfl

theorem record {E F A : Type} (f : E → F) (make : Result A → E) (call : Result A) :
 run f (NJU_Log.record make call)=NJU_Log.record (f ∘ make) call := rfl

/-- One event at SAME arguments, including an aborting raw Result. -/
theorem raw (n : Usize) (r : Reader) :
 run event (NJU_Log.record (fun reply=>⟨r,reply⟩) (NJC_ConcreteUnwrap.raw n r))=
 NJU_ResumeObserved.recordRaw n r := rfl

#print axioms result
#print axioms pure
#print axioms bind
#print axioms record
#print axioms raw
end NKK_EmbedRaw
