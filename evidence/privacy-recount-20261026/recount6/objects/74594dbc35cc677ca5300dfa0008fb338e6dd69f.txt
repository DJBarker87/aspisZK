import R1Z.PV_RW_NativeForModel
import R1Z.PV_RW_ResultListRun
set_option autoImplicit false
namespace R1Z.PV_RW_NativeForList
open Aeneas Aeneas.Std Result
open PV_RW_NativeForSource

theorem exact {S : Type} (step : U32 → S → Result S) (iterator : Iter) (state : S) :
    PV_RW_NativeForSource.run step iterator state=
      PV_RW_ResultListRun.run step (PV_RW_Cursor.remaining (PV_RW_NativeCursor.cursor iterator)) state := by
  apply PV_RW_ResultOutcome.injective
  rw [PV_RW_NativeForModel.run,PV_RW_ResultListRun.model]

theorem initial {S : Type} (step : U32 → S → Result S) (values : Slice U32) (state : S) :
    PV_RW_NativeForSource.run step (⟨values,0⟩ : Iter) state=
      PV_RW_ResultListRun.run step values.val state := by
  exact exact step (⟨values,0⟩ : Iter) state
#print axioms exact
#print axioms initial
end R1Z.PV_RW_NativeForList
