import Aeneas
import EbyKPushExplicitTypesV1
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1EbyKPushExplicitOpsV1

abbrev Wide := AspisR1EbyKPushCutV3.field.wide_exact.WideExact
abbrev Qm := AspisR1EbyKPushCutV3.field.QM31
abbrev Q := AspisR1EbyKPushCutV3.fast_pairing.canonical.Q
abbrev Dot := AspisR1EbyKPushCutV3.fast_pairing.canonical.Dot
abbrev State := AspisR1EbyKPushCutV3.fast_pairing.EbyKDot

@[irreducible] def maxTerms : Std.Usize := 4096#usize

/-- Verbatim emitted EbyKDot.push body with the external callees made explicit
    parameters: `from_wide`, `checked_q`, `Dot.push`, and checked Usize add. -/
def pushWithOps
    (fromWide : Wide → Result (Array Q 2#usize))
    (checkedQ : Qm → Result (core.result.Result Q Unit))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (value : Wide) (scalar : Qm) :
    Result ((core.result.Result Unit Unit) × State) := do
  if self.count >= maxTerms
  then ok (core.result.Result.Err (), self)
  else
    let a ← fromWide value
    let value_c0 ← Array.index_usize a 0#usize
    let value_c1 ← Array.index_usize a 1#usize
    let r ← checkedQ scalar
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let d ← pushDot self.c0 value_c0 val
      let d1 ← pushDot self.c1 value_c1 val
      let i ← addUsize self.count 1#usize
      ok (core.result.Result.Ok (), { c0 := d, c1 := d1, count := i })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame Unit) residual
      ok (r1, self)

theorem result_bind_ok_inv {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : Bind.bind r f = Result.ok y) :
    ∃ x, r = Result.ok x ∧ f x = Result.ok y := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp [Bind.bind, Aeneas.Std.bind] at h
  | div => simp [Bind.bind, Aeneas.Std.bind] at h

@[simp] theorem result_bind_eq_ok_iff {α β : Type} (r : Result α) (f : α → Result β) (y : β) :
    Bind.bind r f = Result.ok y ↔ ∃ x, r = Result.ok x ∧ f x = Result.ok y := by
  constructor
  · exact result_bind_ok_inv r f y
  · rintro ⟨x, rfl, h⟩
    exact h

theorem from_residual_never_ok_ok (res : core.result.Result core.convert.Infallible Unit) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame Unit) res ≠ .ok (.Ok ()) := by
  cases res with
  | Ok impossible => cases impossible
  | Err err => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame, Aeneas.Std.bind]

theorem push_success_below_bound
    (fromWide : Wide → Result (Array Q 2#usize))
    (checkedQ : Qm → Result (core.result.Result Q Unit))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (value : Wide) (scalar : Qm) (out : State)
    (h : pushWithOps fromWide checkedQ pushDot addUsize self value scalar =
      .ok (.Ok (), out)) :
    self.count < maxTerms := by
  by_contra hn
  have hg : self.count >= maxTerms := le_of_not_gt hn
  have hguard : pushWithOps fromWide checkedQ pushDot addUsize self value scalar =
      .ok (.Err (), self) := by
    simp only [pushWithOps, if_pos hg]
  rw [hguard] at h
  cases h

theorem push_success_state_shape
    (fromWide : Wide → Result (Array Q 2#usize))
    (checkedQ : Qm → Result (core.result.Result Q Unit))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (value : Wide) (scalar : Qm) (out : State)
    (h : pushWithOps fromWide checkedQ pushDot addUsize self value scalar =
      .ok (.Ok (), out)) :
    ∃ a x0 x1 r val d0 d1 i,
      fromWide value = .ok a ∧
      Array.index_usize a 0#usize = .ok x0 ∧
      Array.index_usize a 1#usize = .ok x1 ∧
      checkedQ scalar = .ok r ∧
      core.result.Result.Insts.CoreOpsTry.branch r =
        .ok (.Continue val) ∧
      pushDot self.c0 x0 val = .ok d0 ∧
      pushDot self.c1 x1 val = .ok d1 ∧
      addUsize self.count 1#usize = .ok i ∧
      out = { c0 := d0, c1 := d1, count := i } := by
  have hbelow := push_success_below_bound fromWide checkedQ pushDot addUsize self value scalar out h
  have hlt : ¬ self.count ≥ maxTerms := not_le_of_gt hbelow
  simp only [pushWithOps, if_neg hlt, result_bind_eq_ok_iff] at h
  rcases h with ⟨a, ha, x0, hx0, x1, hx1, r, hr, cf, hcf, hmatch⟩
  cases cf with
  | Continue val =>
      simp only [result_bind_eq_ok_iff] at hmatch
      rcases hmatch with ⟨d0, hd0, d1, hd1, i, hi, hout⟩
      exact ⟨a, x0, x1, r, val, d0, d1, i, ha, hx0, hx1, hr, hcf, hd0, hd1, hi,
        by simpa using hout.symm⟩
  | Break residual =>
      cases r with
      | Ok q =>
          simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf
      | Err err =>
          have hres : residual = .Err err := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf.symm
          subst residual
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, Aeneas.Std.bind] at hmatch

#print axioms from_residual_never_ok_ok
#print axioms push_success_below_bound
#print axioms push_success_state_shape
end AspisR1EbyKPushExplicitOpsV1
