import T2Nat_ReadCongr
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_Try
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq

def withOk {A B : Type} (r : Result (core.result.Result A verifier.Error))
    (k : A → Result (core.result.Result B verifier.Error)) :
    Result (core.result.Result B verifier.Error) := do
  let value ← r
  match value with
  | .Err e => ok (.Err e)
  | .Ok a => k a

def withRead {A B : Type} (r : Result (core.result.Result A verifier.Error × verifier.Reader))
    (k : A → verifier.Reader → Result (core.result.Result B verifier.Error)) :
    Result (core.result.Result B verifier.Error) := do
  let (value,out) ← r
  match value with
  | .Err e => ok (.Err e)
  | .Ok a => k a out

theorem branch {A B : Type} (r : core.result.Result A verifier.Error)
    (k : A → Result (core.result.Result B verifier.Error)) :
    (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue a => k a
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          B (core.convert.FromSame verifier.Error) residual) =
    (match r with | .Err e => ok (.Err e) | .Ok a => k a) := by
  cases r <;> rfl

theorem read_congr {A B : Type}
    {r s : Result (core.result.Result A verifier.Error × verifier.Reader)}
    (same : EqOk r s)
    (k l : A → verifier.Reader → Result (core.result.Result B verifier.Error))
    (next : ∀ a out, EqOk (k a out) (l a out)) :
    EqOk (withRead r k) (withRead s l) := by
  unfold withRead
  apply T2Nat_ResultEq.bind same
  rintro ⟨value,out⟩
  cases value with
  | Err e => exact T2Nat_ResultEq.refl _
  | Ok a => exact next a out

theorem ok_congr {A B : Type}
    {r s : Result (core.result.Result A verifier.Error)} (same : EqOk r s)
    (k l : A → Result (core.result.Result B verifier.Error))
    (next : ∀ a, EqOk (k a) (l a)) : EqOk (withOk r k) (withOk s l) := by
  unfold withOk
  apply T2Nat_ResultEq.bind same
  intro value
  cases value with
  | Err e => exact T2Nat_ResultEq.refl _
  | Ok a => exact next a

#print axioms branch
#print axioms read_congr
#print axioms ok_congr
end AspisR1.T2Nat_Try
end
