import GSScalarFactorEnvelopeM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSScalarRootEnvelopeM10
open CompPoly Polynomial GSScalarOperandEnvelopeM10
open GSScalarCallScheduleM10 CompPolyPolynomialBackendBridge CompPolyCompleteRoots
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem roots_bounded (p : CPolynomial K) (q t D : Nat) (H : Nat → Fin t → K × K)
    (hp : p.toPoly.Monic) (hd : p.toPoly.natDegree ≤ D) (hD : 1 ≤ D) :
    ∀ c ∈ (GSScalarSequentialScheduleM10.roots p q t H).2, Bounded D q c := by
  have ha := power_degree CPolynomial.X p q hp
  have hx : (CPolynomial.X : CPolynomial K).toPoly.natDegree ≤ D := by
    simpa only [CPolynomial.X_toPoly, Polynomial.natDegree_X] using hD
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
  have ht := GSScalarFactorEnvelopeM10.factor_bounded q t H (p.natDegree+1) 0 0 D
    (rootFactor p q) hm hf hD
  intro c hc
  change c ∈ [.power CPolynomial.X p q,
    .gcd p (modPower CPolynomial.X p q-CPolynomial.X)]++_ at hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨stored_size_of_degree _ D hx, stored_size_of_degree _ D hd,
        Nat.le_refl _,hp⟩
    · exact ⟨stored_size_of_degree _ D hd,stored_size_of_degree _ D hs⟩
  · exact ht c hc

theorem general_bounded (p : CPolynomial K) (q t D : Nat)
    (H : Nat → Fin t → K × K) (hd : p.toPoly.natDegree ≤ D) (hD : 1 ≤ D) :
    ∀ c ∈ (GSScalarSequentialScheduleM10.general p q t H).2, Bounded D q c := by
  unfold GSScalarSequentialScheduleM10.general
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
        simpa only [CPolynomial.ringEquiv_apply, CPolynomial.toPoly_zero] using hz
      have hm : (CPolynomial.monicNormalize p).toPoly.Monic := by
        rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
        exact Polynomial.monic_normalize hn
      exact roots_bounded _ q t D H hm
        ((CompPolyGeneralRootsProgram.normalized_natDegree p).le.trans hd) hD

#print axioms roots_bounded
#print axioms general_bounded
end AspisR1.GSScalarRootEnvelopeM10
end
