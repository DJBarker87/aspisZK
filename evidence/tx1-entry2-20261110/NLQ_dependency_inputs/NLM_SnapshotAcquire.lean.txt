import NLM_SnapshotState
set_option autoImplicit false
noncomputable section
namespace NLM_Snapshot
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLF_RefCell NLF_SdkModel
/-- This is the concrete source state before one wrapper occurrence. -/
def ready (e : Entry) (token : Nat) (owned : List Owned) : State :=
 ⟨e,(NLM_RuntimeInput.initial e).state,token,owned⟩
def guard (s : State) (a : Nat) : Guard := ⟨(s.sdk.accounts a).data,s.next,.shared⟩
def acquired (s : State) (a : Nat) : NLF_SdkModel.State :=
 put s.sdk (s.sdk.accounts a).data
  {s.sdk.cells (s.sdk.accounts a).data with readers := s.next::(s.sdk.cells (s.sdk.accounts a).data).readers}
def live (s : State) (a : Nat) : State := {s with sdk := acquired s a,next:=s.next+1}
theorem acquire (e : Entry) (t a : Nat) (owned : List Owned) :
 try_borrow_data (ready e t owned).sdk a (ready e t owned).next =
 (acquired (ready e t owned) a,.ok (guard (ready e t owned) a)) := by
 apply shared_result <;> simp [ready,NLM_RuntimeInput.initial,NLF_RuntimeInterpretation.install,NLF_Admission.initial]
theorem current_payload (e : Entry) (t a : Nat) (owned : List Owned) :
 (deref (acquired (ready e t owned) a) (guard (ready e t owned) a)).bytes =
 AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1) := by
 rw [show deref (acquired (ready e t owned) a) (guard (ready e t owned) a)=
  ((ready e t owned).sdk.cells ((ready e t owned).sdk.accounts a).data).payload from shared_deref _ _ _]
 exact NLM_RuntimeInput.initial_payload e a
theorem release_current (e : Entry) (t a : Nat) (owned : List Owned) :
 release (acquired (ready e t owned) a) (guard (ready e t owned) a)=.ok (ready e t owned).sdk := by
 apply shared_release
 rfl
#print acquire
#print current_payload
#print release_current
#print axioms acquire
#print axioms current_payload
#print axioms release_current
end NLM_Snapshot
