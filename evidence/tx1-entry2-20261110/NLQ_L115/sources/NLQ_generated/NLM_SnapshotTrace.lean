import NLM_SnapshotReturn
import NLM_SnapshotPrefix
set_option autoImplicit false
noncomputable section
namespace NLM_Snapshot
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLF_RefCell NLF_SdkModel
def normalEvents (s : State) (a lo hi : Nat) : List Event :=
 [.acquire s a s.next (acquired s a) (.ok (.ok (guard s a))),
  .deref (live s a) (guard s a) (.ok (deref (acquired s a) (guard s a)))] ++
 (if (deref (acquired s a) (guard s a)).bytes.length=lo ∨
     (deref (acquired s a) (guard s a)).bytes.length=hi
  then [.allocate (live s a) (guard s a) (deref (acquired s a) (guard s a)).bytes.length (.ok ())]
  else []) ++
 [.release (live s a) (guard s a) (.ok (.ok s.sdk)),
  .returned (live s a) a lo hi (.ok (s.input.snapshot a lo hi))]
/-- Complete local trace, not just its Result projection. Every deferred
length error has already released the SAME guard before returning Owned. -/
theorem normal (e : Entry) (t a lo hi : Nat) (owned : List Owned) :
 G (ready e t owned) a lo hi (.ok ()) =
 ⟨.ok (e.snapshot a lo hi,returned (ready e t owned) a lo hi),
   normalEvents (ready e t owned) a lo hi⟩ := by
 unfold G
 rw [acquire]
 simp only [Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,bind_tc_ok]
 rw [release_current]
 split <;> simp_all [Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,
  normalEvents,live,returned,ready,acquired,guard,shared_deref,List.append_assoc]
#print normal
#print axioms normal
end NLM_Snapshot
