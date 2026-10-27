import R0P.Copy
import FJh_Base
import JGa_PatternBounds
set_option autoImplicit false
namespace AspisR1.FJk_CopyPatternDescriptor
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open FJh_Base (cell)
def model (p : CompiledPoolV1PairForestPattern) : R0P.CopyPattern where
  kinds := fun i=>(cell p.kinds i).val
  columns := fun i=>⟨(cell p.columns i).val%16,Nat.mod_lt _ (by decide)⟩
  offsets := fun i=>(cell p.offsets i).val
/-- Small literal descriptor registry, checked without field arithmetic. -/
theorem registry (i : Fin 14) :
    model (cell constants.COPY_PATTERNS i)=R0P.copyPatterns i := by
  fin_cases i <;>
    simp only [constants.COPY_PATTERNS,Array.make,cell,model,
      pattern00,pattern01,pattern02,pattern03,pattern04,pattern05,pattern06,pattern07,
      pattern08,pattern09,pattern10,pattern11,pattern12,pattern13]
  all_goals rfl
#print axioms registry
end AspisR1.FJk_CopyPatternDescriptor
