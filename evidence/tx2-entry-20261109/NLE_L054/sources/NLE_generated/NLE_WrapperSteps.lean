import NLE_WrapperSource
set_option autoImplicit false
noncomputable section
namespace NLE_Wrapper
open Aeneas Aeneas.Std Result
/-- Every snapshot receives the SAME original runtime account at that index;
only the owned snapshot list is appended, with no input frame mutation. -/
theorem snapshot_frame {Account : Type} (state : State Account) (value : Owned) :
 ({state with snapshots := state.snapshots ++ [value]} : State Account).frame = state.frame := rfl
/-- The one returned state is used in the subsequent cut, also for deferred
snapshot bytes errors: a snapshot itself returns Owned, not ProgramResult. -/
theorem snapshot_result {Account : Type} (ops : Ops Account) (state : State Account)
 (index min max : Usize) : (snapshot ops state index min max).result = (do
 let account ← state.frame.accounts.index_usize index
 let value ← ops.snapshot account min max
 ok (value,{state with snapshots := state.snapshots ++ [value]})) := by
 simp only [snapshot,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_liftM,NJU_Log.erase_pure]
/-- Exact empty request, full runtime clear reply, no reclassification as a
Boolean successful-clear premise. -/
theorem clear_result {Account : Type} (ops : Ops Account) (state : State Account) :
 (clear ops state).result = ops.clear ⟨[],by simp⟩ := rfl
#print snapshot_result
#print clear_result
#print axioms snapshot_frame
#print axioms snapshot_result
#print axioms clear_result
end NLE_Wrapper
