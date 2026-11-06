import NLM_SevenTrace
set_option autoImplicit false
noncomputable section
namespace NLM_DeferredContinuation
open Aeneas Aeneas.Std NLM_Snapshot NLM_SevenSnapshots AspisR1.S2W_D189Entry
/-- A bad-length snapshot is a returned owned value, not an outer abort.
The remaining real snapshot sites must still execute in chronological order. -/
theorem suffix (e : Entry) (t a lo hi : Nat) (owned : List NLM_Snapshot.Owned)
 (rest : List Site) :
 NLM_SevenSnapshots.G (fun _=>.ok ()) (⟨a,lo,hi⟩::rest) (ready e t owned)=
 ⟨.ok (ready e (t+1+rest.length)
    ((owned++[e.snapshot a lo hi])++ownedValues e rest)),
   normalEvents (ready e t owned) a lo hi ++
   chronological e (t+1) (owned++[e.snapshot a lo hi]) rest⟩ := by
 rw [NLM_SevenSnapshots.G,NLM_Snapshot.normal]
 change (⟨(NLM_SevenSnapshots.G (fun _=>.ok ()) rest
  (ready e (t+1) (owned++[e.snapshot a lo hi]))).result,
  normalEvents (ready e t owned) a lo hi++(NLM_SevenSnapshots.G (fun _=>.ok ()) rest
  (ready e (t+1) (owned++[e.snapshot a lo hi]))).events⟩ : NLM_Snapshot.Run NLM_Snapshot.State)=_
 rw [NLM_SevenSnapshots.normal]
#print suffix
#print axioms suffix
end NLM_DeferredContinuation
