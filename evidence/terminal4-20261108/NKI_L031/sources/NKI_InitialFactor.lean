import NKI_InitialPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialFactor
open Aeneas Aeneas.Std Result FIq_Native
open NKI_InitialPrefix (Public Openings Selectors Tail)
def literal (p : Public) (o : Openings) (s : Selectors) : Result (Array field.QM31 16#usize × Array field.QM31 16#usize) := do
 let t←NKI_InitialPrefix.run p o s
 let absorption←pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal t.low t.fixed t.two t.eight t.nodes o.z
 ok (t.initial,absorption)
/-- Pure Result-bind factoring of the SAME complete emitted body; no new
extraction, no primitive evaluation or source-success premise. -/
theorem source (p : Public) (o : Openings) (s : Selectors) :
 literal p o s=pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption p o s := by
 simp only [literal,NKI_InitialPrefix.run,pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption,Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
 congr 1
#print axioms source
end AspisR1.NKI_InitialFactor
end
