import NGW_ConstructorQM
import NGW_ConstructorArrays
import NGW_Reverse
set_option autoImplicit false
namespace NGW_StepModel
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM

def step (z successor : Array Q 10#usize) (carry : Q) (i : Usize) :
    Result (Array Q 10#usize × Q) := do
  let bit ← Array.index_usize z i
  let product ← FIn_WeightsExtract.field.QM31.mul bit carry
  let sum ← FIn_WeightsExtract.field.QM31.add bit carry
  let twice ← FIn_WeightsExtract.field.QM31.add product product
  let value ← FIn_WeightsExtract.field.QM31.sub sum twice
  let out ← Array.update successor i value
  ok (out,product)

theorem iteration (z successor : Array Q 10#usize) (carry : Q)
    (iter cursor : NGW_Reverse.Rev) (i : Usize)
    (advance : NGW_Reverse.next iter=ok (some i,cursor)) :
    FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body z iter successor carry =
      (do let (out,next) ← step z successor carry i; ok (cont (cursor,out,next))) := by
  unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body step
  unfold NGW_Reverse.next at advance
  rw [advance]
  simp only [bind_tc_ok,bind_assoc_eq]

#print axioms iteration
end NGW_StepModel
