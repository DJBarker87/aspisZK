import BatchedWeightsActualReducer
import AspisR1BatchedFoldSourceStep
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsFlushPrimitiveV2
open AspisR1.ExtractedCurrentReducer
abbrev U64 := UScalar UScalarTy.U64

def generatedFlush (x : U64) : Result U64 := do
  let low ← lift (x &&& 2147483647#u64)
  let high ← x >>> 31#i32
  low + high

theorem generatedFlush_eq_foldExecution (x : U64) :
    generatedFlush x = foldExecution x := by
  simp only [generatedFlush, foldExecution, lift, bind_tc_ok,
    UScalar.and, UScalar.shiftRight, UScalar.add]
  rfl

theorem generatedFlush_success (x : U64) :
    ∃ y : U64, generatedFlush x = .ok y ∧
      y.val = AspisR1BatchedFoldSourceStep.fold x.val := by
  rw [generatedFlush_eq_foldExecution]
  obtain ⟨y, hy, hv⟩ := foldExecution_success x
  refine ⟨y, hy, ?_⟩
  rw [hv]
  rw [AspisV8R17.RawReducer.foldBits_eq_fold31]
  rfl
#print axioms generatedFlush_success
end BatchedWeightsFlushPrimitiveV2
