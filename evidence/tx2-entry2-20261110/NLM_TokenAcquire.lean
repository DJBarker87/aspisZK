import NLM_TokenEvents
set_option autoImplicit false
noncomputable section
namespace NLM_TokenAcquire
open Aeneas Aeneas.Std NLF_RefCell NLF_SdkModel NLM_Snapshot
/-- The exact SDK Parent before THIS source occurrence; prior events frame. -/
def parent (s : NLM_Snapshot.State) (events : List NLF_ParentModel.Event) : NLF_ParentModel.Parent :=
 ⟨s.sdk,s.next,events⟩
theorem acquire (e : AspisR1.S2W_D189Entry.Entry) (t a : Nat)
 (owned : List NLM_Snapshot.Owned) (events : List NLF_ParentModel.Event) :
 NLF_ParentModel.acquire (parent (ready e t owned) events) a .shared=
 (⟨acquired (ready e t owned) a,t+1,
    events++[.acquire a t .shared (.ok (guard (ready e t owned) a))]⟩,
   .ok (guard (ready e t owned) a)) := by
 unfold NLF_ParentModel.acquire
 change (let r := try_borrow_data (ready e t owned).sdk a t
         ((⟨r.1,t+1,events++[.acquire a t .shared r.2]⟩ : NLF_ParentModel.Parent),r.2))=_
 have h := NLM_Snapshot.acquire e t a owned
 change try_borrow_data (ready e t owned).sdk a t=_ at h
 rw [h]
#print acquire
#print axioms acquire
end NLM_TokenAcquire
