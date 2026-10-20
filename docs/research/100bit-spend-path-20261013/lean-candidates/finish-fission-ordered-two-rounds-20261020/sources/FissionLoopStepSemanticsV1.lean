import Aeneas
import FinishCandidateEquations
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FinishFissionProof
open _root_.AspisR1FinishRelationCurrent

abbrev Range := core.ops.range.Range Usize

/-- Captured fields of the generated loop body. -/
structure RoundEnvironment where
  v : verifier.View
  v1 : transport.Variant
  inactive : aspis_core.field.WideExact
  foldedRoot : Option (Array U8 32#usize)
  v2 : transport.Variant
  roots : Array (Array U8 32#usize) 2#usize
  gamma : aspis_core.field.WideExact
  kappa : aspis_core.field.WideExact
  alpha : Array aspis_core.field.WideExact 2#usize
  rho : aspis_core.field.QM31
  queries : Array U32 22#usize
  semanticAlpha : Array aspis_core.field.QM31 10#usize
  z : Array aspis_core.circle.SecureCirclePoint 2#usize
  preparedClaim : aspis_core.field.WideExact
  state : Array U8 32#usize

def assembledView (e : RoundEnvironment) : verifier.View :=
  { e.v with variant := e.v1, inactive := e.inactive, folded_root := e.foldedRoot }

def assembledPrepared (e : RoundEnvironment) : verifier.Prepared :=
  { variant := e.v2, roots := e.roots, gamma := e.gamma, kappa := e.kappa,
    alpha := e.alpha, rho := e.rho, queries := e.queries,
    semantic_alpha := e.semanticAlpha, z := e.z, claim := e.preparedClaim,
    state := e.state }

def capturedStep {ε : Type}
    (step : verifier.View → verifier.Prepared → aspis_core.field.WideExact → Usize →
      Result (core.result.Result aspis_core.field.WideExact ε))
    (env : RoundEnvironment) : Usize → aspis_core.field.WideExact →
      Result (core.result.Result aspis_core.field.WideExact ε) :=
  fun round claim => step (assembledView env) (assembledPrepared env) claim round

/-- Exact emitted loop-body control flow, with only its helper implementation
    replaced by the explicit `step` parameter. -/
def bodyAdapter {ε : Type}
    (step : verifier.View → verifier.Prepared → aspis_core.field.WideExact → Usize →
      Result (core.result.Result aspis_core.field.WideExact ε))
    (env : RoundEnvironment) (iter : Range) (claim : aspis_core.field.WideExact) :
    Result (ControlFlow (Range × aspis_core.field.WideExact)
      (aspis_core.field.WideExact × Option (core.result.Result aspis_core.field.WideExact ε))) := do
  let (o1, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o1 with
  | none => ok (done (claim, none))
  | some round =>
    let r ← step (assembledView env) (assembledPrepared env) claim round
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val => ok (cont (iter1, val))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.WideExact (core.convert.FromSame ε) residual
      ok (done (claim, some return_capture))

def loopAdapter {ε : Type}
    (step : verifier.View → verifier.Prepared → aspis_core.field.WideExact → Usize →
      Result (core.result.Result aspis_core.field.WideExact ε))
    (env : RoundEnvironment) (iter : Range) (claim : aspis_core.field.WideExact) :
    Result (aspis_core.field.WideExact × Option (core.result.Result aspis_core.field.WideExact ε)) :=
  Aeneas.Std.loop (fun s : Range × aspis_core.field.WideExact =>
    bodyAdapter step env s.1 s.2) (iter, claim)

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

theorem loopAdapter_two_rounds {ε : Type}
    (step : verifier.View → verifier.Prepared → aspis_core.field.WideExact → Usize →
      Result (core.result.Result aspis_core.field.WideExact ε))
    (env : RoundEnvironment) (i0 i1 i2 : Range)
    (c0 c1 c2 : aspis_core.field.WideExact)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hnext1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i1 =
      .ok (some i1.start, i2))
    (hnext2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i2 =
      .ok (none, i2))
    (hstep0 : capturedStep step env i0.start c0 = .ok (.Ok c1))
    (hstep1 : capturedStep step env i1.start c1 = .ok (.Ok c2)) :
    loopAdapter step env i0 c0 = .ok (c2, none) := by
  have hstep0' := hstep0
  have hstep1' := hstep1
  simp only [capturedStep] at hstep0' hstep1'
  have hb0 : bodyAdapter step env i0 c0 = .ok (.cont (i1, c1)) := by
    simp [bodyAdapter, hnext0, hstep0',
      core.result.Result.Insts.CoreOpsTry.branch]
  have hb1 : bodyAdapter step env i1 c1 = .ok (.cont (i2, c2)) := by
    simp [bodyAdapter, hnext1, hstep1',
      core.result.Result.Insts.CoreOpsTry.branch]
  have hb2 : bodyAdapter step env i2 c2 = .ok (.done (c2, none)) := by
    simp [bodyAdapter, hnext2]
  unfold loopAdapter
  rw [Aeneas.Std.loop.eq_def]
  simp only [hb0]
  rw [Aeneas.Std.loop.eq_def]
  simp only [hb1]
  rw [Aeneas.Std.loop.eq_def]
  simp only [hb2]

theorem loopAdapter_first_error {ε : Type}
    (step : verifier.View → verifier.Prepared → aspis_core.field.WideExact → Usize →
      Result (core.result.Result aspis_core.field.WideExact ε))
    (env : RoundEnvironment) (i0 i1 : Range)
    (c0 : aspis_core.field.WideExact) (e : ε)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hstep0 : capturedStep step env i0.start c0 = .ok (.Err e)) :
    bodyAdapter step env i0 c0 = .ok (.done (c0, some (.Err e))) := by
  unfold bodyAdapter capturedStep at *
  simp only [hnext0, bind_tc_ok]
  simp [hstep0, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem loopAdapter_first_error_propagates {ε : Type}
    (step : verifier.View → verifier.Prepared → aspis_core.field.WideExact → Usize →
      Result (core.result.Result aspis_core.field.WideExact ε))
    (env : RoundEnvironment) (i0 i1 : Range)
    (c0 : aspis_core.field.WideExact) (e : ε)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hstep0 : capturedStep step env i0.start c0 = .ok (.Err e)) :
    loopAdapter step env i0 c0 = .ok (c0, some (.Err e)) := by
  unfold loopAdapter
  rw [Aeneas.Std.loop.eq_def]
  have hb := loopAdapter_first_error step env i0 i1 c0 e hnext0 hstep0
  simpa only [hb, bind_tc_ok]

theorem loopAdapter_two_rounds_explicit_ops
    {W D : Type}
    (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = .ok true → x = y)
    (step : verifier.View → verifier.Prepared → aspis_core.field.WideExact → Usize →
      Result (core.result.Result aspis_core.field.WideExact verifier.Error))
    (env : RoundEnvironment) (i0 i1 i2 : Range)
    (c0 c1 c2 : aspis_core.field.WideExact)
    (poly0 poly1 : Slice U8) (alpha0 alpha1 : aspis_core.field.WideExact)
    (hnext0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i0 =
      .ok (some i0.start, i1))
    (hnext1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i1 =
      .ok (some i1.start, i2))
    (hnext2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize i2 =
      .ok (none, i2))
    (hstep0 : capturedStep step env i0.start c0 = .ok (.Ok c1))
    (hstep1 : capturedStep step env i1.start c1 = .ok (.Ok c2))
    (hmodel0 : capturedStep step env i0.start c0 =
      verifier.finish_relation_round ops poly0 alpha0 c0 i0.start)
    (hmodel1 : capturedStep step env i1.start c1 =
      verifier.finish_relation_round ops poly1 alpha1 c1 i1.start) :
    loopAdapter step env i0 c0 = .ok (c2, none) ∧
      FinishCandidateEquations.RoundEquation ops poly0 alpha0 c0 c1 ∧
      FinishCandidateEquations.RoundEquation ops poly1 alpha1 c1 c2 := by
  have hcall0 := hmodel0.symm.trans hstep0
  have hcall1 := hmodel1.symm.trans hstep1
  have heq0 := FinishCandidateEquations.round_equation
    ops faithful poly0 alpha0 c0 c1 i0.start hcall0
  have heq1 := FinishCandidateEquations.round_equation
    ops faithful poly1 alpha1 c1 c2 i1.start hcall1
  exact ⟨loopAdapter_two_rounds step env i0 i1 i2 c0 c1 c2
    hnext0 hnext1 hnext2 hstep0 hstep1, heq0, heq1⟩

#print axioms bodyAdapter
#print axioms loopAdapter_two_rounds
#print axioms loopAdapter_first_error
#print axioms loopAdapter_first_error_propagates
#print axioms loopAdapter_two_rounds_explicit_ops
end AspisR1FinishFissionProof
