import R1Z.PV_RW_NativeForList
import R1Z.PV_RW_ResultListTotal
set_option autoImplicit false
namespace R1Z.PV_RW_NativeForConcat
open Aeneas Aeneas.Std Result
open PV_RW_NativeForSource

theorem split {S : Type} (step : U32 → S → Result S) (left right joined : Slice U32)
    (shape : joined.val=left.val++right.val) (state : S) :
    PV_RW_NativeForSource.run step (⟨joined,0⟩ : Iter) state=(do
      let middle ← PV_RW_NativeForSource.run step (⟨left,0⟩ : Iter) state
      PV_RW_NativeForSource.run step (⟨right,0⟩ : Iter) middle) := by
  simp only [PV_RW_NativeForList.initial]
  rw [shape]
  exact PV_RW_ResultListTotal.append step left.val right.val state
#print axioms split
end R1Z.PV_RW_NativeForConcat
