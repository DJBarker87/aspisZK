import AspisV8R19.R366SemanticNormalization

/-! Source-shaped wire reconstruction and terminal-guard compatibility.
The operations match the selected semantic_cached omitted-linear convention.
This is not yet an execution refinement of Rust field/array/transcript code,
a source degree proof for the honest terminal, or joint mask coverage. -/
set_option autoImplicit false
namespace AspisR19.R368WireSemanticCompatibility
open AspisV8R17 Polynomial R366SemanticNormalization
open scoped BigOperators
variable {F : Type*} [Field F] [NeZero (2 : F)]

noncomputable def wirePolynomial (carry constant : F) (high : Fin 26 → F) : F[X] :=
  C (carry/2) + roundPolynomial (constant-carry/2) high

theorem wire_eval (carry constant : F) (high : Fin 26 → F) (x : F) :
    (wirePolynomial carry constant high).eval x=
      semanticRound carry (constant-carry/2) high x := by
  simp only [wirePolynomial,eval_add,eval_C,roundPolynomial_eval,semanticRound]

theorem wire_degree (carry constant : F) (high : Fin 26 → F) :
    (wirePolynomial carry constant high).natDegree ≤ 27 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact roundPolynomial_degree _ _

theorem wire_boundary (carry constant : F) (high : Fin 26 → F) :
    (wirePolynomial carry constant high).eval 0+
      (wirePolynomial carry constant high).eval 1=carry := by
  rw [wire_eval,wire_eval]
  exact semanticRound_boundary _ _ _

theorem wire_constant (carry constant : F) (high : Fin 26 → F) :
    (wirePolynomial carry constant high).coeff 0=constant := by
  simp only [wirePolynomial,coeff_add,coeff_C_zero,roundPolynomial_coeff_zero]
  ring

theorem wire_high (carry constant : F) (high : Fin 26 → F) (i : Fin 26) :
    (wirePolynomial carry constant high).coeff (i.val+2)=high i := by
  simp only [wirePolynomial,coeff_add,roundPolynomial_coeff_high,
    coeff_C,show i.val+2≠0 by omega,if_false,zero_add]

/-- Exact omitted coefficient used by selected semantic_cached, including its carry. -/
theorem wire_linear (carry constant : F) (high : Fin 26 → F) :
    (wirePolynomial carry constant high).coeff 1=
      carry-(constant+constant+∑ i,high i) := by
  have hb := wire_boundary carry constant high
  have hd := wire_degree carry constant high
  have h1 := finite_expansion (wirePolynomial carry constant high) hd 1
  have h0 := wire_constant carry constant high
  have ht : tail (wirePolynomial carry constant high)=high := by
    funext i
    exact wire_high _ _ _ i
  rw [eval_zero,h0,h1,ht] at hb
  simp only [one_pow,mul_one] at hb
  linear_combination hb

noncomputable def wireRounds : (r : Nat) → F → RoundCoins (F × (Fin 26 → F)) r →
    RoundCoins F r → RoundCoins F[X] r
  | 0, _, _, _ => PUnit.unit
  | r+1, carry, sent, z =>
      let p := wirePolynomial carry sent.1.1 sent.1.2
      (p,wireRounds r (p.eval z.1) sent.2 z.2)

theorem wire_walk_valid (r : Nat) (carry : F)
    (sent : RoundCoins (F × (Fin 26 → F)) r) (z : RoundCoins F r) :
    validWalk r carry (wireRounds r carry sent z) z := by
  induction r generalizing carry with
  | zero => trivial
  | succ r ih =>
    exact ⟨wire_degree _ _ _,wire_boundary _ _ _,ih _ sent.2 z.2⟩

/-- The terminal check keeps an existing error and rejects a false carry. -/
def terminalGuard {E : Type*} [DecidableEq F] (terminalError : E)
    (result : Except E F) (claim : F) : Except E Unit :=
  result.bind (fun actual => if actual=claim then .ok () else .error terminalError)

theorem terminal_guard_ok {E : Type*} [DecidableEq F] (terminalError : E)
    (result : Except E F) (claim : F) :
    terminalGuard terminalError result claim=.ok () ↔ result=.ok claim := by
  cases result with
  | error e => simp [terminalGuard,Except.bind]
  | ok actual =>
    by_cases h : actual=claim
    · subst actual; simp [terminalGuard,Except.bind]
    · simp [terminalGuard,Except.bind,h]

theorem terminal_guard_error {E : Type*} [DecidableEq F] (terminalError e : E)
    (claim : F) : terminalGuard terminalError (.error e) claim=.error e := rfl

/-- Two accepted records with the SAME retained terminal result have compatible
semantic coordinates. Degree/boundary facts are derived from wire reconstruction,
not assumed. Equality of retained source terminal inputs remains a source gate. -/
theorem accepted_wire_compatibility {E : Type*} [DecidableEq F]
    (terminalError : E) (result : Except E F) (a b : F)
    (sa sb : RoundCoins (F × (Fin 26 → F)) 10) (z : RoundCoins F 10)
    (ha : terminalGuard terminalError result (walk 10 a (wireRounds 10 a sa z) z)=.ok ())
    (hb : terminalGuard terminalError result (walk 10 b (wireRounds 10 b sb z) z)=.ok ()) :
    (∑ i : Fin 271,maskWeights271 (1/2:F) z i *
      maskCoins271 (a-b) (subtractCoins 10
        (coordinates 10 a (wireRounds 10 a sa z) z)
        (coordinates 10 b (wireRounds 10 b sb z) z)) i)=0 := by
  have hea := (terminal_guard_ok terminalError result _).mp ha
  have heb := (terminal_guard_ok terminalError result _).mp hb
  have he : walk 10 a (wireRounds 10 a sa z) z=walk 10 b (wireRounds 10 b sb z) z := by
    exact Except.ok.inj (hea.symm.trans heb)
  exact full_271_compatibility a b _ _ z (wire_walk_valid 10 a sa z)
    (wire_walk_valid 10 b sb z) he

#print axioms wire_eval
#print axioms wire_degree
#print axioms wire_boundary
#print axioms wire_constant
#print axioms wire_high
#print axioms wire_linear
#print axioms wire_walk_valid
#print axioms terminal_guard_ok
#print axioms terminal_guard_error
#print axioms accepted_wire_compatibility
end AspisR19.R368WireSemanticCompatibility
