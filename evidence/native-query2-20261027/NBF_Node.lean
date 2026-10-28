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
 obtain ⟨square,hs,hsv,hsc⟩ := ExtractedCurrentReducer.current_mul_mod z z
 obtain ⟨doubled,hd,hdv,hdc⟩ := ExtractedCurrentM31AddSub.current_add_mod square square hsc hsc
 obtain ⟨node,hn,hnv,hnc⟩ := ExtractedCurrentM31AddSub.current_sub_mod doubled 1#u32 hdc (by decide)
 refine ⟨node,?_,hnc⟩
 simp only [source,NBF_Accumulate.install,NBF_RowInstall.install,NBF_BasisInstall.install,
   hs,hd,hn,bind_tc_ok]
#print axioms total_canonical
end NBF_Node
