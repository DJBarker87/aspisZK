import AspisV8R19.FixedQueryChordScale
import AspisV8R19.FixedQueryNonzero

/-! Algebraic source gate only. No IID challenges, conditional query law,
retry/publication bound or whole-protocol privacy conclusion is assumed. -/
namespace AspisR19.FixedQuerySourceGate
open AspisV8R17 FixedQueryPolynomial
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem source_determinant (half quarter tau : F) (previous : Fin 271 → F)
    (t : Fin 22 → F) (ht : Function.Injective t) (s : Fin 36 → F)
    (hu : 1+(s 12)^2≠0) (hv : 1+(s 13)^2≠0) :
    (FixedQuerySource.matrix half quarter
      (rationalX (s 12)*rationalY (s 13)-rationalY (s 12)*rationalX (s 13))
      (rationalY (s 12)-rationalY (s 13)) (rationalX (s 13)-rationalX (s 12))
      (s 10) (s 11) tau (fun i => s ⟨i.val,by omega⟩) previous t).det=
      chordScale (s 12) (s 13)^13*
        MvPolynomial.eval s (polynomial half quarter (FixedQuerySource.querySection t ht)).det := by
  rw [FixedQuerySource.matrix_eq _ _ _ _ _ _ _ _ _ _ _ ht,
    FixedQueryChordScale.rational_determinant _ _ _ _ _ _ _ _ hu hv,determinant_evaluation]
  rfl

theorem source_nonsingular_iff (half quarter tau : F) (previous : Fin 271 → F)
    (t : Fin 22 → F) (ht : Function.Injective t) (s : Fin 36 → F)
    (hu : 1+(s 12)^2≠0) (hv : 1+(s 13)^2≠0) (hne : s 13≠s 12) :
    (FixedQuerySource.matrix half quarter
      (rationalX (s 12)*rationalY (s 13)-rationalY (s 12)*rationalX (s 13))
      (rationalY (s 12)-rationalY (s 13)) (rationalX (s 13)-rationalX (s 12))
      (s 10) (s 11) tau (fun i => s ⟨i.val,by omega⟩) previous t).det≠0 ↔
      MvPolynomial.eval s (polynomial half quarter (FixedQuerySource.querySection t ht)).det≠0 := by
  rw [source_determinant half quarter tau previous t ht s hu hv]
  have hs := chordScale_ne_zero (s 12) (s 13) (NeZero.ne 2) hu hv hne
  simp [hs]

#print axioms source_determinant
#print axioms source_nonsingular_iff
end
end AspisR19.FixedQuerySourceGate
