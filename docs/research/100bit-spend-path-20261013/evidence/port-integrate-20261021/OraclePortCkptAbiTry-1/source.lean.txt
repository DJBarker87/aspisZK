import Stage2ContinuationResumeBody

/-! Success inversion for the extracted Rust Result/Reader sequencing. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbiTry
open AspisR1Stage2

abbrev tryBind {A B : Type} (r : core.result.Result A verifier.Error)
    (k : A → Result (core.result.Result B verifier.Error)) :
    Result (core.result.Result B verifier.Error) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue x => k x
  | .Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        B (core.convert.FromSame verifier.Error) residual

theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (do let x ← m; k x) = ok out) : ∃ x, m = ok x ∧ k x = ok out := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem try_success {A B : Type} (r : core.result.Result A verifier.Error)
    (k : A → Result (core.result.Result B verifier.Error)) (out : B)
    (h : tryBind r k = ok (.Ok out)) :
    ∃ x, r = .Ok x ∧ k x = ok (.Ok out) := by
  cases r with
  | Ok x => exact ⟨x,rfl,h⟩
  | Err e => cases h

theorem read_success {A B : Type}
    (m : Result (core.result.Result A verifier.Error × verifier.Reader))
    (k : A → verifier.Reader → Result (core.result.Result B verifier.Error)) (out : B)
    (h : (do let (r,reader) ← m; tryBind r (fun x => k x reader)) = ok (.Ok out)) :
    ∃ x reader, m = ok (.Ok x,reader) ∧ k x reader = ok (.Ok out) := by
  obtain ⟨⟨r,reader⟩,call,tail⟩ := bind_success _ _ _ h
  obtain ⟨x,eq,tail⟩ := try_success _ _ _ tail
  subst r
  exact ⟨x,reader,call,tail⟩

#print axioms bind_success
#print axioms try_success
#print axioms read_success
end AspisR1.OraclePortCkptAbiTry
