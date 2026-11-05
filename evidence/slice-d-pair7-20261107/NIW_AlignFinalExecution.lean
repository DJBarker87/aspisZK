import NIW_AlignFieldReply
import NIT_FinalCompleteness
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinalExecution
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

def step (parts powers : Parts) (kind : Usize) (before : E) : Result (E×Final) := do
 let lhs := epick powers kind.val
 let rhs := epick parts kind.val
 let product←FIo_Native.aspis_core.field.wide_exact.WideExact.mul lhs rhs
 let reply←FIo_Native.aspis_core.field.wide_exact.WideExact.add before product
 ok (reply,⟨lhs,rhs,product,before,product,reply,2,[0,1]⟩)

theorem observed (parts powers : Parts) (hp : canonical parts) (hk : canonical powers)
 (kind : Usize) (small : kind.val<7) (before : E) (hb : canonE before) :
 NIW_AlignFieldReply.Produced (step parts powers kind before) (fun result=>
  cutFinal parts powers kind.val before result.2 result.1 ∧
  EMul result.2.mul_a result.2.mul_b result.2.product ∧
  EAdd result.2.add_a result.2.add_b result.2.reply ∧ canonE result.1) := by
 let lhs := epick powers kind.val
 let rhs := epick parts kind.val
 have actual := NIW_AlignFieldReply.em lhs rhs (epick_canonical powers hk _) (epick_canonical parts hp _)
 cases call : FIo_Native.aspis_core.field.wide_exact.WideExact.mul lhs rhs with
 | fail err => simp only [call,NIW_AlignFieldReply.Produced] at actual
 | div => simp only [call,NIW_AlignFieldReply.Produced] at actual
 | ok product =>
  simp only [call,NIW_AlignFieldReply.Produced] at actual
  have addition := NIW_AlignFieldReply.ea before product hb actual.2
  cases added : FIo_Native.aspis_core.field.wide_exact.WideExact.add before product with
  | fail err => simp only [added,NIW_AlignFieldReply.Produced] at addition
  | div => simp only [added,NIW_AlignFieldReply.Produced] at addition
  | ok reply =>
   simp only [added,NIW_AlignFieldReply.Produced] at addition
   unfold step
   dsimp only
   change FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    (epick powers kind.val) (epick parts kind.val)=ok product at call
   rw [call,bind_tc_ok,added,bind_tc_ok]
   exact ⟨⟨small,hp,hk,hb,actual.2,addition.2,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    actual.1,addition.1,addition.2⟩

#print axioms observed
end AspisR1.NIW_AlignFinalExecution
