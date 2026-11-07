import NLQ_Stage1State
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Ready
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
/-- Fixed source snapshot outputs, with the SAME input buffers and installed
SDK cell map. The three successful allocation arms are local branches only. -/
def initial (e : S2W_D189Entry.Entry) : State := ⟨NLQ_SnapshotFold.final e,none⟩
theorem token (e : S2W_D189Entry.Entry) : (initial e).snapshots.next=3 := rfl
theorem accounts (e : S2W_D189Entry.Entry) :
 (initial e).snapshots.owned = e.first.val := rfl
theorem sdk (e : S2W_D189Entry.Entry) :
 (initial e).snapshots.sdk=(NLM_RuntimeInput.initial e).state := rfl
#print axioms token
#print axioms accounts
#print axioms sdk
end NLQ_Stage1Ready
