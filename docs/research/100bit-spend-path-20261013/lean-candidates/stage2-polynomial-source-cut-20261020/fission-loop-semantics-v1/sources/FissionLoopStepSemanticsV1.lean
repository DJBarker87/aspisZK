import Aeneas
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
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (claim, none))
  | some round =>
      let r ← step round claim
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | ControlFlow.Continue val => ok (cont (iter1, val))
      | ControlFlow.Break residual =>
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
  | fail e => simp only [hs, bind_tc_fail] at h
  | div => simp only [hs, bind_tc_div] at h
  | ok cf =>
    cases cf with
    | done result => simp only [hs, bind_tc_ok] at h; subst result; exact Or.inl rfl
    | cont stateNext => simp only [hs, bind_tc_ok] at h; exact Or.inr ⟨stateNext, rfl, h⟩

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
  simp only [bodyAdapter, hnext0, bind_tc_ok, hstep0]
  rw [Aeneas.Std.loop.eq_def]
  simp only [bodyAdapter, hnext1, bind_tc_ok, hstep1]
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
  simp only [hnext0, bind_tc_ok, hstep0]
  rfl

#print axioms bodyAdapter
#print axioms loopAdapter_two_rounds
#print axioms loopAdapter_first_error
end AspisR1FinishFissionProof
