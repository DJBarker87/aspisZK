import NLM_TokenAcquire
set_option autoImplicit false
noncomputable section
namespace NLM_TokenDeref
open Aeneas Aeneas.Std NLF_RefCell NLF_SdkModel NLM_Snapshot
/-- Admission supplies cell identity; token liveness follows from the actual
shared acquisition on this source-initial state. -/
theorem live (e : AspisR1.S2W_D189Entry.Entry) (t a : Nat) (owned : List NLM_Snapshot.Owned) :
 NLF_RefCell.live ((acquired (ready e t owned) a).cells (guard (ready e t owned) a).cell)
  (guard (ready e t owned) a).token (guard (ready e t owned) a).kind := by
 simp [NLF_RefCell.live,NLM_Snapshot.acquired,NLM_Snapshot.guard,NLF_SdkModel.put,NLM_Snapshot.ready,NLM_RuntimeInput.initial,
  NLF_RuntimeInterpretation.install,NLF_Admission.initial]

theorem deref (e : AspisR1.S2W_D189Entry.Entry) (t a : Nat)
 (owned : List NLM_Snapshot.Owned) (events : List NLF_ParentModel.Event) :
 NLF_ParentModel.deref ⟨acquired (ready e t owned) a,t+1,events⟩ (guard (ready e t owned) a)=
 (⟨acquired (ready e t owned) a,t+1,
    events++[.deref (guard (ready e t owned) a)
     (.ok (NLF_SdkModel.deref (acquired (ready e t owned) a) (guard (ready e t owned) a)))]⟩,
  .ok (NLF_SdkModel.deref (acquired (ready e t owned) a) (guard (ready e t owned) a))) := by
 simp only [NLF_ParentModel.deref,if_pos (live e t a owned)]
#print live
#print deref
#print axioms live
#print axioms deref
end NLM_TokenDeref
