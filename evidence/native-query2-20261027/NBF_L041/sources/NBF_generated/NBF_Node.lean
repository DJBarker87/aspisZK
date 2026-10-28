import NBF_PowerStep
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_Node
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Exact node expression at the SAME query's line_z read. -/
def source (ops : Ops) (z : U32) : Result U32 := do
 let square ← (NBF_Accumulate.install ops).op7 z z
 let doubled ← (NBF_Accumulate.install ops).op8 square
 let one ← (NBF_Accumulate.install ops).op5
 (NBF_Accumulate.install ops).op6 doubled one

theorem total_canonical (ops : Ops) (z : U32) :
 ∃ node, source ops z=ok node ∧ node.val<2^31-1 := by
 have same : source ops z=S7Kani3BasisOuter.t2 z := rfl
 rw [same]
 exact S7Kani3BasisOuter.t2_total z
#print axioms total_canonical
end NBF_Node
