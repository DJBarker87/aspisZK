import GSScalarTraceFieldWorkM10

/-! Scalar traces at a nonzero outer RR tape cursor. Nested sequentialization
changes query addresses but preserves the observed root output and outer
cursor. This is the deterministic bridge needed for a whole RR trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.GSScalarAtCursorM10
open CompPoly GSScalarCallScheduleM10 GSScalarOperandEnvelopeM10
open AspisV8R19.MemoizedProgramLaw
open SequentialFreshProgram CompPolySequentialAbortBound CompPolyCompleteRoots
open CompPolyPolynomialBackendBridge
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem double_sequential {I A O : Type} (H : Nat → A) (p : Program I A O)
    (localCursor cursor : Nat) :
    ((eval H (sequential (sequential p localCursor) cursor)).2.1.1,
      (eval H (sequential (sequential p localCursor) cursor)).2.2) =
      (eval H (sequential p cursor)).2 := by
  induction p generalizing localCursor cursor with
  | done o => rfl
  | ask i next ih => exact ih (H cursor) (localCursor+1) (cursor+1)

def roots (p : CPolynomial K) (q t : Nat) (H : Nat → Fin t → K × K) (cursor : Nat) :
    (Option (List K) × Nat) × List (Call K) :=
  let a := modPower CPolynomial.X p q
  let r := GSScalarSequentialScheduleM10.factor q t H (p.natDegree+1) 0 cursor
    (CPolynomial.gcdMonic p (a-CPolynomial.X))
  (r.1,[.power CPolynomial.X p q,.gcd p (a-CPolynomial.X)]++r.2)

theorem roots_value (p : CPolynomial K) (q t : Nat) (H : Nat → Fin t → K × K) (cursor : Nat) :
    (roots p q t H cursor).1 =
      ((eval H (sequential (rootsProgram p q t) cursor)).2.1.1,
        (eval H (sequential (rootsProgram p q t) cursor)).2.2) := by
  simp only [roots,GSScalarSequentialScheduleM10.factor_value,rootsProgram,rootFactor]
  exact (double_sequential H _ 0 cursor).symm

def general (p : CPolynomial K) (q t : Nat) (H : Nat → Fin t → K × K) (cursor : Nat) :
    (Option (List K) × Nat) × List (Call K) :=
  if p == 0 then ((none,cursor),[]) else
  if p.natDegree = 0 then ((some [],cursor),[]) else
    roots (CPolynomial.monicNormalize p) q t H cursor

theorem value (p : CPolynomial K) (q t : Nat) (H : Nat → Fin t → K × K) (cursor : Nat) :
    (general p q t H cursor).1 =
      ((eval H (sequential (CompPolyGeneralRootsProgram.generalRootsProgram p q t) cursor)).2.1.1,
        (eval H (sequential (CompPolyGeneralRootsProgram.generalRootsProgram p q t) cursor)).2.2) := by
  simp only [general,CompPolyGeneralRootsProgram.generalRootsProgram]
  split
  · rfl
  · split
    · rfl
    · exact roots_value _ _ _ _ _

theorem roots_length (p : CPolynomial K) (q t : Nat) (H : Nat → Fin t → K × K) (cursor : Nat) :
    (roots p q t H cursor).2.length ≤ 2+fuelBudget t (p.natDegree+1) := by
  have h := GSScalarSequentialScheduleM10.factor_length q t H (p.natDegree+1) 0 cursor
    (rootFactor p q)
  simpa only [roots,List.length_append,List.length_cons,List.length_nil,rootFactor] using
    Nat.add_le_add_left h 2

theorem roots_bounded (p : CPolynomial K) (q t D : Nat) (H : Nat → Fin t → K × K)
    (cursor : Nat) (hp : p.toPoly.Monic) (hd : p.toPoly.natDegree ≤ D) (hD : 1 ≤ D) :
    ∀ c ∈ (roots p q t H cursor).2, Bounded D q c := by
  have ha := power_degree CPolynomial.X p q hp
  have hx : (CPolynomial.X : CPolynomial K).toPoly.natDegree ≤ D := by
    simpa only [CPolynomial.X_toPoly,Polynomial.natDegree_X] using hD
  have hs : (modPower CPolynomial.X p q-CPolynomial.X).toPoly.natDegree ≤ D := by
    rw [CPolynomial.toPoly_sub]
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (ha.trans hd) hx)
  have hb := rootFactor_backend_correct p q hp
  have hm : (rootFactor p q).toPoly.Monic := by
    rw [hb]
    exact FiniteFieldNormalizedRootFactor.rootFactor_monic _ _ hp.ne_zero
  have hf : (rootFactor p q).toPoly.natDegree ≤ D := by
    rw [hb]
    exact (Polynomial.natDegree_le_of_dvd
      (FiniteFieldNormalizedRootFactor.rootFactor_dvd _ _) hp.ne_zero).trans hd
  have ht := GSScalarFactorEnvelopeM10.factor_bounded q t H (p.natDegree+1) 0 cursor D
    (rootFactor p q) hm hf hD
  intro c hc
  change c ∈ [.power CPolynomial.X p q,.gcd p (modPower CPolynomial.X p q-CPolynomial.X)]++_ at hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨stored_size_of_degree _ D hx,stored_size_of_degree _ D hd,Nat.le_refl _,hp⟩
    · exact ⟨stored_size_of_degree _ D hd,stored_size_of_degree _ D hs⟩
  · exact ht c hc

theorem bounded (p : CPolynomial K) (q t D : Nat) (H : Nat → Fin t → K × K)
    (cursor : Nat) (hd : p.toPoly.natDegree ≤ D) (hD : 1 ≤ D) :
    ∀ c ∈ (general p q t H cursor).2, Bounded D q c := by
  unfold general
  split
  · simp
  · rename_i hp
    split
    · simp
    · have hn : p.toPoly ≠ 0 := by
        intro hz
        apply hp
        apply beq_iff_eq.mpr
        apply CPolynomial.ringEquiv.injective
        simpa only [CPolynomial.ringEquiv_apply,CPolynomial.toPoly_zero] using hz
      have hm : (CPolynomial.monicNormalize p).toPoly.Monic := by
        rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
        exact Polynomial.monic_normalize hn
      exact roots_bounded _ q t D H cursor hm
        ((CompPolyGeneralRootsProgram.normalized_natDegree p).le.trans hd) hD

#print axioms double_sequential
#print axioms roots_value
#print axioms value
#print axioms roots_length
#print axioms roots_bounded
#print axioms bounded
end AspisR1.GSScalarAtCursorM10
end
