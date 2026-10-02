import AspisV8R17.SourceMaskLoop

/-! Source-shaped G cancellation for the research terminal. The original
semantic composition and positive-transfer correction do not read G.
Rust array/index/field refinement and source coverage remain separate. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [Field F]

/-- `payment_terminal` subtracts the old explicit-G mask contribution and
adds the structured-G value. `base` retains all C1/H1 nonlinear terms. -/
def replacedGTerminal (base factor g extra : F) : F :=
  (base + factor * g) - g * factor + g + extra

theorem replacedGTerminal_eq (base factor g extra : F) :
    replacedGTerminal base factor g extra = base + extra + g := by
  unfold replacedGTerminal
  ring

theorem replacedGTerminal_shift (base factor g extra delta : F) :
    replacedGTerminal base factor (g + delta) extra -
      replacedGTerminal base factor g extra = delta := by
  simp only [replacedGTerminal_eq]
  ring

/-- Comparing contexts with the SAME old G removes it even when their
C1/H1-dependent base terms differ nonlinearly. -/
theorem witness_target_independent_of_G
    (left right factor g leftExtra rightExtra : F) :
    replacedGTerminal right factor g rightExtra -
      replacedGTerminal left factor g leftExtra =
      (right + rightExtra) - (left + leftExtra) := by
  simp only [replacedGTerminal_eq]
  ring

theorem roundEval_add {n : ℕ} (a da : F) (b db : Fin n → F) (x : F) :
    roundEval (a + da) (fun i => b i + db i) x =
      roundEval a b x + roundEval da db x := by
  simp only [roundEval, add_mul, Finset.sum_add_distrib]
  ring

theorem sourceMaskLoop_add (half carry delta : F) (xs ys : List F)
    (h : xs.length = ys.length) :
    sourceMaskLoop half (carry + delta) (List.zipWith (· + ·) xs ys) =
      sourceMaskLoop half carry xs + sourceMaskLoop half delta ys := by
  induction xs generalizing ys carry delta with
  | nil =>
    cases ys with
    | nil => simp [sourceMaskLoop_nil]
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zipWith_cons_cons, sourceMaskLoop_cons]
      rw [show (carry + delta) * half + (x + y) =
        (carry * half + x) + (delta * half + y) by ring]
      exact ih (carry := carry * half + x) (delta := delta * half + y) (ys := ys) h

/-- The old G term cancels pointwise, so it also cancels before any
Boolean-suffix aggregation. No linearity of the non-G terminal is needed. -/
theorem cube_target_independent_of_G [NeZero (2 : F)]
    (r : ℕ) (left right factor g le re : RoundCoins F r → F) :
    cubeSum r (fun z => replacedGTerminal (right z) (factor z) (g z) (re z) -
      replacedGTerminal (left z) (factor z) (g z) (le z)) =
    cubeSum r (fun z => (right z + re z) - (left z + le z)) := by
  congr 1
  funext z
  exact witness_target_independent_of_G _ _ _ _ _ _

#print axioms replacedGTerminal_eq
#print axioms replacedGTerminal_shift
#print axioms witness_target_independent_of_G
#print axioms roundEval_add
#print axioms sourceMaskLoop_add
#print axioms cube_target_independent_of_G
end AspisV8R17
