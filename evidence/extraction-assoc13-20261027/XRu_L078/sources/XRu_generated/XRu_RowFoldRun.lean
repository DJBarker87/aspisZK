import XRu_RowFold
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowFoldRun
open XRu_RowFold
theorem source (a b c d x0 x1 x2 x3 : U64) (back : Back)
 (h0 : AspisR1.ExtractedCurrentReducer.foldExecution a=ok x0)
 (h1 : AspisR1.ExtractedCurrentReducer.foldExecution b=ok x1)
 (h2 : AspisR1.ExtractedCurrentReducer.foldExecution c=ok x2)
 (h3 : AspisR1.ExtractedCurrentReducer.foldExecution d=ok x3) :
 loop step (it a b c d 0,back)=ok (fun r => back (put 0 x0 (put 1 x1 (put 2 x2 (put 3 x3 r))))) := by
 rw [loop.eq_def,step0 a b c d x0 back h0]
 simp only [bind_tc_ok]
 rw [loop.eq_def,step1 a b c d x1 _ h1]
 simp only [bind_tc_ok]
 rw [loop.eq_def,step2 a b c d x2 _ h2]
 simp only [bind_tc_ok]
 rw [loop.eq_def,step3 a b c d x3 _ h3]
 simp only [bind_tc_ok]
 rw [loop.eq_def,stop]
#print axioms source
/-- The enclosing actual mutable restoration applies every returned write. -/
theorem restore (a b c d x0 x1 x2 x3 : U64)
 (h0 : AspisR1.ExtractedCurrentReducer.foldExecution a=ok x0)
 (h1 : AspisR1.ExtractedCurrentReducer.foldExecution b=ok x1)
 (h2 : AspisR1.ExtractedCurrentReducer.foldExecution c=ok x2)
 (h3 : AspisR1.ExtractedCurrentReducer.foldExecution d=ok x3) :
 (do
  let (iter,intoBack) ← XRn_Join_intoIter (row a b c d)
  let back ← verifier.update_residue_row_loop1 iter id
  ok (intoBack back))=ok (row x0 x1 x2 x3) := by
 unfold XRn_Join_intoIter
 simp only [bind_tc_ok]
 change (do
  let back ← loop step (it a b c d 0,id)
  ok (Array.from_slice (row a b c d) (back (it a b c d 0)).slice))=_
 rw [source a b c d x0 x1 x2 x3 id h0 h1 h2 h3]
 rfl
#print axioms restore
end XRu_RowFoldRun
