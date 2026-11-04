import NFF_LoggedStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_InnerCut
open Aeneas Aeneas.Std Result ControlFlow

/-- Original borrowed input places and values, fixed for the entire slot.
Native admission must bind the places to these values; this is not inferred
from address equality. -/
structure Input where
  q : Array U8 608#usize
  g : NEV_DotInputs.Coefficients
  slot : Usize
  qPlace : Nat
  gPlace : Nat

structure Cut where
  input : Input
  iter : core.ops.range.Range Usize
  sums : Array U64 8#usize

structure Returned where
  input : Input
  sums : Array U64 8#usize

def step (oracle : NFF_LoggedEight.Oracle) (before : Cut) :
    Result (ControlFlow Cut Returned) := do
  let out ← NFF_LoggedStep.step oracle before.input.q before.input.g
    before.input.slot before.iter before.sums
  match out with
  | done sums => ok (done ⟨before.input,sums⟩)
  | cont (iter,sums) => ok (cont ⟨before.input,iter,sums⟩)

def erase (out : ControlFlow Cut Returned) :
    ControlFlow (core.ops.range.Range Usize × Array U64 8#usize) (Array U64 8#usize) :=
  match out with
  | done out => done out.sums
  | cont out => cont (out.iter,out.sums)

theorem same_input (oracle : NFF_LoggedEight.Oracle) (before : Cut)
    (after : ControlFlow Cut Returned) (success : step oracle before=ok after) :
    match after with
    | done out => out.input=before.input
    | cont out => out.input=before.input := by
  unfold step at success
  cases h : NFF_LoggedStep.step oracle before.input.q before.input.g
    before.input.slot before.iter before.sums with
  | fail e => simp only [h,bind_tc_fail] at success; cases success
  | div => simp only [h,bind_tc_div] at success; cases success
  | ok out =>
    cases out with
    | done sums => simp only [h,bind_tc_ok] at success; cases success; rfl
    | cont next => rcases next with ⟨iter,sums⟩; simp only [h,bind_tc_ok] at success; cases success; rfl

theorem erased (oracle : NFF_LoggedEight.Oracle) (before : Cut) :
    (do let out ← step oracle before; ok (erase out)) =
      NFF_LoggedStep.step oracle before.input.q before.input.g
        before.input.slot before.iter before.sums := by
  unfold step
  cases h : NFF_LoggedStep.step oracle before.input.q before.input.g
    before.input.slot before.iter before.sums with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok out => cases out <;> simp [h,erase]

#print axioms same_input
#print axioms erased
end AspisR1.NFI_InnerCut
end
