import CuSavingsGammaTable

/-! Relate the complete emitted preparations after erasing ephemeral scratch.
The local claim-factor equation is explicit and must be discharged by the
claim source bridge; it is not an assumed whole-verifier equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace AspisR1.CuSavingsGammaPreparation
open Aeneas Aeneas.Std Result AspisR1CuGamma
open CuSavingsGammaTable
variable [Boundaries]

def erase {A : Type} (m : Result (A × Table)) : Result A := do
  let pair ← m
  .ok pair.1

private theorem bind_ext {A B : Type} (m : Result A) (f g : A → Result B)
    (h : ∀ x, f x = g x) : (do let x ← m; f x) = (do let x ← m; g x) := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok x => exact h x

private theorem tail_eq (gamma : E)
    (oldClaim : Result (core.result.Result E Err))
    (newClaim : Table → Result (core.result.Result E Err))
    (make : E → Prepared)
    (factor : oldClaim = (do let g ← weights.powers 29#usize gamma; newClaim g)) :
    (do
      let r ← oldClaim
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue value => .ok (.Ok (make value))
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Prepared (core.convert.FromSame Err) residual) =
      erase (finishWithTable gamma newClaim make) := by
  rw [factor]
  unfold erase finishWithTable
  simp only [bind_assoc_eq]
  apply bind_ext
  intro g
  apply bind_ext
  intro r
  cases r <;> rfl

theorem preparations_eq {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (initial : Table)
    (claim_factor : ∀ gamma kappa,
      gamma_old.prepared_claim D sem v.y1 v.inactive gamma kappa =
        (do let g ← weights.powers 29#usize gamma
            gamma_new.prepared_claim D sem v.y1 v.inactive g kappa)) :
    gamma_old.Prepared.gamma_old_new D sem v hash =
      erase (gamma_new.Prepared.gamma_new_new D sem v hash initial) := by
  unfold gamma_old.Prepared.gamma_old_new gamma_new.Prepared.gamma_new_new erase
  simp only [bind_assoc_eq,lift,bind_tc_ok]
  apply bind_ext
  intro state
  apply bind_ext
  intro t
  apply bind_ext
  rintro ⟨gamma,t1⟩
  simp only [uncurry_apply_pair,bind_assoc_eq]
  apply bind_ext
  intro inactiveBytes
  apply bind_ext
  rintro ⟨kappa,t2⟩
  simp only [uncurry_apply_pair,bind_assoc_eq]
  apply bind_ext
  rintro ⟨alpha0,t3⟩
  simp only [uncurry_apply_pair,bind_assoc_eq]
  apply bind_ext
  intro folds
  split
  · simp only [bind_assoc_eq]
    apply bind_ext
    intro capacity
    apply bind_ext
    intro root
    apply bind_ext
    intro bytes1
    apply bind_ext
    intro bytes2
    apply bind_ext
    rintro ⟨alpha1,t4⟩
    simp only [uncurry_apply_pair,bind_assoc_eq]
    apply bind_ext
    rintro ⟨r,t5⟩
    simp only [uncurry_apply_pair,bind_assoc_eq]
    cases r with
    | Err error => rfl
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,bind_assoc_eq]
      apply bind_ext
      intro row
      apply bind_ext
      rintro ⟨rho,t6⟩
      simp only [uncurry_apply_pair,bind_assoc_eq]
      exact tail_eq gamma _ _ _ (claim_factor gamma kappa)
  · simp only [bind_assoc_eq]
    apply bind_ext
    rintro ⟨r,t4⟩
    simp only [uncurry_apply_pair,bind_assoc_eq]
    cases r with
    | Err error => rfl
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,bind_assoc_eq]
      apply bind_ext
      intro row
      apply bind_ext
      rintro ⟨rho,t5⟩
      simp only [uncurry_apply_pair,bind_assoc_eq]
      exact tail_eq gamma _ _ _ (claim_factor gamma kappa)

#print axioms erase
#print axioms preparations_eq
end AspisR1.CuSavingsGammaPreparation
