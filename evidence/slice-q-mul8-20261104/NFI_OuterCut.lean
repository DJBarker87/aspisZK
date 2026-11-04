import NFI_InnerCut
import NFF_LoggedOuterStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_OuterCut
open Aeneas Aeneas.Std Result ControlFlow

abbrev Input := NFI_InnerCut.Input

structure Cut where
  input : Input
  iter : NFA_Iterator.Iter
  limbs : Array U64 8#usize

structure Returned where
  input : Input
  limbs : Array U64 8#usize

def step (oracle : NFF_LoggedEight.Oracle) (before : Cut) :
    Result (ControlFlow Cut Returned) := do
  let out ← NFF_LoggedOuterStep.step oracle before.input.q before.input.g
    before.input.slot before.iter before.limbs
  match out with
  | done limbs => ok (done ⟨before.input,limbs⟩)
  | cont (iter,limbs) => ok (cont ⟨before.input,iter,limbs⟩)

def erase (out : ControlFlow Cut Returned) :
    ControlFlow (NFA_Iterator.Iter × Array U64 8#usize) (Array U64 8#usize) :=
  match out with
  | done out => done out.limbs
  | cont out => cont (out.iter,out.limbs)

theorem same_input (oracle : NFF_LoggedEight.Oracle) (before : Cut)
    (after : ControlFlow Cut Returned) (success : step oracle before=ok after) :
    match after with
    | done out => out.input=before.input
    | cont out => out.input=before.input := by
  unfold step at success
  cases h : NFF_LoggedOuterStep.step oracle before.input.q before.input.g
    before.input.slot before.iter before.limbs with
  | fail e => simp only [h,bind_tc_fail] at success; cases success
  | div => simp only [h,bind_tc_div] at success; cases success
  | ok out =>
    cases out with
    | done limbs => simp only [h,bind_tc_ok] at success; cases success; rfl
    | cont next => rcases next with ⟨iter,limbs⟩; simp only [h,bind_tc_ok] at success; cases success; rfl

theorem erased (oracle : NFF_LoggedEight.Oracle) (before : Cut) :
    (do let out ← step oracle before; ok (erase out)) =
      NFF_LoggedOuterStep.step oracle before.input.q before.input.g
        before.input.slot before.iter before.limbs := by
  unfold step
  cases h : NFF_LoggedOuterStep.step oracle before.input.q before.input.g
    before.input.slot before.iter before.limbs with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok out => cases out <;> simp [h,erase]

#print axioms same_input
#print axioms erased
end AspisR1.NFI_OuterCut
end
