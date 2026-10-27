import R0P.Copy
import RPu_FJh_Base
import RPu_JGa_PatternBounds
set_option autoImplicit false
namespace AspisR1.FJk_CopyPatternDescriptor
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open FJh_Base (cell)
def model (p : CompiledPoolV1PairForestPattern) : R0P.CopyPattern where
  kinds := fun i=>(cell p.kinds i).val
  columns := fun i=>⟨(cell p.columns i).val%16,Nat.mod_lt _ (by decide)⟩
  offsets := fun i=>(cell p.offsets i).val
end AspisR1.FJk_CopyPatternDescriptor
