import XSa_FinishWord
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_FinishFour
open AspisR1EbyKFinish.Proof

theorem four (a b c d : U64) :
 XRn_Join_dotFinish ⟨Array.make 4#usize [a,b,c,d]⟩ =
 ok (XRn_Join_q [word a,word b,word c,word d]) := by
 unfold XRn_Join_dotFinish
 simp only [Array.make,List.mapM_cons,List.mapM_nil,XSa_FinishWord.reduce,bind_tc_ok]

#print axioms four
end XSa_FinishFour
