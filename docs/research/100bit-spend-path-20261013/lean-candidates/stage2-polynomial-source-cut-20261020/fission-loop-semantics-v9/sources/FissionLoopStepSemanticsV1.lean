import Aeneas
import FinishCandidateEquations
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FinishFissionProof

abbrev Range := core.ops.range.Range Usize

/-- Parameterized copy of the generated loop-body control flow. The sole source
    substitution is the actual helper call, represented by `step`. -/
def bodyAdapter {α ε : Type}
    (step : Usize → α → Result (core.result.Result α ε))
    (iter : Range) (claim : α) :
    Result (ControlFlow (Range × α) (α × Option (core.result.Result α ε))) := do
  let pair ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  let o := pair.1
  let iter1 := pair.2
  match o with
  | none => ok (done (claim, none))
  | some round =>
      let r ← step round claim
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => ok (cont (iter1, val))
      | core.ops.control_flow.ControlFlow.Break residual =>
          let return_capture ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              α (core.convert.FromSame ε) residual
          ok (done (claim, some return_capture))

def loopAdapter {α ε : Type}
    (step : Usize → α → Result (core.result.Result α ε))
    (iter : Range) (claim : α) :
    Result (α × Option (core.result.Result α ε)) :=
  Aeneas.Std.loop (fun s : Range × α => bodyAdapter step s.1 s.2) (iter, claim)

private theorem loop_success_cases {α β : Type}
    (step : α → Result (ControlFlow α β)) (state : α) (out : β)
    (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp only [hs] at h; cases h
  | div => simp only [hs] at h; cases h
  | ok cf =>
    simp only [hs] at h
    cases cf with
    | done result =>
      have heq : result = out := Result.ok.inj h
      subst out
      exact Or.inl rfl
    | cont stateNext => exact Or.inr ⟨stateNext, rfl, h⟩

theorem loopAdapter_two_rounds {α ε : Type}
    (step : Usize → α → Result (core.result.Result α ε))
    (i0 i1 i2 : Range) (c0 c1 c2 : α)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hnext1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i1 =
      .ok (some i1.start, i2))
    (hnext2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i2 =
      .ok (none, i2))
    (hstep0 : step i0.start c0 = .ok (.Ok c1))
    (hstep1 : step i1.start c1 = .ok (.Ok c2)) :
    loopAdapter step i0 c0 = .ok (c2, none) := by
  unfold loopAdapter
  rw [Aeneas.Std.loop.eq_def]
  simp only [bodyAdapter, hnext0, bind_tc_ok]
  simp only [hstep0, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def]
  simp only [bodyAdapter, hnext1, bind_tc_ok]
  simp only [hstep1, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def]
  simp only [bodyAdapter, hnext2, bind_tc_ok]

theorem loopAdapter_first_error {α ε : Type}
    (step : Usize → α → Result (core.result.Result α ε))
    (i0 i1 : Range) (c0 : α) (e : ε)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hstep0 : step i0.start c0 = .ok (.Err e)) :
    bodyAdapter step i0 c0 = .ok (.done (c0, some (.Err e))) := by
  unfold bodyAdapter
  simp only [hnext0, bind_tc_ok]
  simp [hstep0, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]


theorem loopAdapter_first_error_propagates {α ε : Type}
    (step : Usize → α → Result (core.result.Result α ε))
    (i0 i1 : Range) (c0 : α) (e : ε)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hstep0 : step i0.start c0 = .ok (.Err e)) :
    loopAdapter step i0 c0 = .ok (c0, some (.Err e)) := by
  unfold loopAdapter
  rw [Aeneas.Std.loop.eq_def]
  have hb := loopAdapter_first_error step i0 i1 c0 e hnext0 hstep0
  simpa only [hb, bind_tc_ok]

theorem loopAdapter_two_rounds_explicit_ops
    {W D : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = .ok true → x = y)
    (step : Usize → aspis_core.field.WideExact →
      Result (core.result.Result aspis_core.field.WideExact verifier.Error))
    (i0 i1 i2 : Range) (c0 c1 c2 : aspis_core.field.WideExact)
    (poly0 poly1 : Slice U8) (alpha0 alpha1 : aspis_core.field.WideExact)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hnext1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i1 =
      .ok (some i1.start, i2))
    (hnext2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i2 =
      .ok (none, i2))
    (hstep0 : step i0.start c0 = .ok (.Ok c1))
    (hstep1 : step i1.start c1 = .ok (.Ok c2))
    (hmodel0 : step i0.start c0 =
      AspisR1FinishRelationCurrent.verifier.finish_relation_round
        ops poly0 alpha0 c0 i0.start)
    (hmodel1 : step i1.start c1 =
      AspisR1FinishRelationCurrent.verifier.finish_relation_round
        ops poly1 alpha1 c1 i1.start) :
    loopAdapter step i0 c0 = .ok (c2, none) ∧
      AspisR1FinishRelationCurrent.FinishCandidateEquations.RoundEquation
        ops poly0 alpha0 c0 c1 ∧
      AspisR1FinishRelationCurrent.FinishCandidateEquations.RoundEquation
        ops poly1 alpha1 c1 c2 := by
  have hcall0 := hstep0.trans hmodel0.symm
  have hcall1 := hstep1.trans hmodel1.symm
  have heq0 := AspisR1FinishRelationCurrent.FinishCandidateEquations.round_equation
    ops faithful poly0 alpha0 c0 c1 i0.start hcall0
  have heq1 := AspisR1FinishRelationCurrent.FinishCandidateEquations.round_equation
    ops faithful poly1 alpha1 c1 c2 i1.start hcall1
  exact ⟨loopAdapter_two_rounds step i0 i1 i2 c0 c1 c2
    hnext0 hnext1 hnext2 hstep0 hstep1, heq0, heq1⟩

#print axioms bodyAdapter
#print axioms loopAdapter_two_rounds
#print axioms loopAdapter_first_error
#print axioms loopAdapter_first_error_propagates
#print axioms loopAdapter_two_rounds_explicit_ops
end AspisR1FinishFissionProof
