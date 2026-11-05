import NHB_FullFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHB_OuterState
open Aeneas Aeneas.Std Result
open NGQ_SamplerDriver
open AspisR1Query31Transcript

def finishCurrent (state : Bytes32) (s : State) : Result Out := do
  let r ← aspis_core.r0_transcript.QueryScan.finish s
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val => ok (.Ok (val,state))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array U32 22#usize × Bytes32)
      (core.convert.FromSame aspis_core.transcript.QuerySampleError) residual

theorem finish_at (advances : Blocks) (index : Usize) (s : State) (bound : index.val<8) :
    finishCurrent (advances.val[index.val]'(by have := advances.property; change advances.val.length=8 at this; omega)) s =
      finishAdvance advances index s := by
  unfold finishCurrent finishAdvance
  rw [NGQ_SamplerArray8.read advances index bound]
  rfl

/-- Explicit native carried state. Continuing does NOT select an advance. -/
def walk (scan : State → Bytes32 → Result (Bool×State)) (advances : Blocks)
    (carried : Bytes32) : List (Bytes32×Usize) → State → Result Out
  | [],s => finishCurrent carried s
  | (block,index)::tail,s => do
      let (stop,next) ← scan s block
      if stop then
        let selected ← Array.index_usize advances index
        finishCurrent selected next
      else walk scan advances carried tail next

/-- Native initial carried=advance7 remains unchanged on every continuing
edge. Stop selects THAT block's advance before finish, including rejection. -/
theorem association (scan : State → Bytes32 → Result (Bool×State))
    (advances : Blocks) (fallback : Usize) (fallbackBound : fallback.val<8)
    (inputs : List (Bytes32×Usize))
    (indices : ∀ p∈inputs,p.2.val<8) (s : State) :
    walk scan advances
      (advances.val[fallback.val]'(by have := advances.property; change advances.val.length=8 at this; omega)) inputs s =
      NGQ_SamplerDriver.walk scan advances fallback inputs s := by
  induction inputs generalizing s with
  | nil => exact finish_at advances fallback s fallbackBound
  | cons head tail ih =>
    have headBound : head.2.val<8 := indices head (List.mem_cons_self ..)
    have tailBound : ∀ p∈tail,p.2.val<8 := fun p hp => indices p (List.mem_cons_of_mem head hp)
    unfold walk NGQ_SamplerDriver.walk
    cases call : scan s head.1 with
    | fail error => rfl
    | div => rfl
    | ok value =>
      rcases value with ⟨stop,next⟩
      simp only [bind_tc_ok]
      dsimp! only
      cases stop with
      | true =>
        simp only [if_true]
        rw [NGQ_SamplerArray8.read advances head.2 headBound,bind_tc_ok]
        exact finish_at advances head.2 next headBound
      | false =>
        simp only [Bool.false_eq_true,if_false]
        exact ih tailBound next

#print axioms finish_at
#print axioms association
end AspisR1.NHB_OuterState
end
