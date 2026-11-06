import NKI_ValuePrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueFactor
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_ValuePrefix (Openings Selectors)
def literal (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) : Result (Array NQ 24#usize) := do
 let t←NKI_ValuePrefix.run o s
 JGa_ValueFinish.run packed t.openings s t.range t.selector
theorem source (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) :
 literal packed o s=pool_v1.pair_forest_semantic_terminal.add_value_lanes packed o s := by
 simp only [literal,NKI_ValuePrefix.run,JGa_ValueFinish.run,
  pool_v1.pair_forest_semantic_terminal.add_value_lanes,Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
 congr 1
#print axioms source
end AspisR1.NKI_ValueFactor
end
