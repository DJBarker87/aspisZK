import CompPolySequentialRootsContract
import SequentialFiniteTapeLaw

namespace AspisR1.CompPolyGeneralRootsProgram
open CompPoly AspisR1.CompPolySequentialAbortBound
open AspisV8R19.MemoizedProgramLaw

/-- General scalar-polynomial root finder. Zero is rejected explicitly;
nonzero constants have no roots; all other inputs use executable monic
normalization before the previously proved sequential root finder. -/
def generalRootsProgram {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (p : CPolynomial K) (q t : Nat) :
    Program Nat (Fin t → K × K) (Option (List K) × Nat) :=
  if p == 0 then .done (none,0) else
  if p.natDegree = 0 then .done (some [],0) else
    rootsProgram (CPolynomial.monicNormalize p) q t

noncomputable section
open Polynomial AspisV8R19.OracleResampling AspisV8PairedCommitment
open AspisR1.SequentialProgramInvariants AspisR1.CompPolySequentialRootsContract
open AspisR1.CompPolyFactorMeanTools
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem normalized_degree (p : CPolynomial K) :
    (CPolynomial.monicNormalize p).toPoly.degree = p.toPoly.degree := by
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize, Polynomial.degree_normalize]

theorem normalized_natDegree (p : CPolynomial K) :
    (CPolynomial.monicNormalize p).toPoly.natDegree = p.toPoly.natDegree :=
  Polynomial.natDegree_eq_of_degree_eq (normalized_degree p)

theorem normalized_roots (p : CPolynomial K) (x : K) :
    IsRoot (CPolynomial.monicNormalize p).toPoly x ↔ IsRoot p.toPoly x := by
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize, ← dvd_iff_isRoot,
    ← dvd_iff_isRoot, dvd_normalize_iff]

theorem constant_no_roots (p : CPolynomial K) (hp : p.toPoly ≠ 0)
    (hd : p.natDegree = 0) (x : K) : ¬ IsRoot p.toPoly x := by
  have hn : p.toPoly.natDegree = 0 := (CPolynomial.natDegree_toPoly p).symm.trans hd
  have he := Polynomial.eq_C_of_natDegree_eq_zero hn
  intro hx
  have hz : p.toPoly.coeff 0 = 0 := by
    simpa only [IsRoot, he, Polynomial.eval_C] using hx
  apply hp
  rw [he, hz, Polynomial.C_0]

/-- Removes the monic and positive-degree premises needed by the core
sampler: actual RR scalar specializations need only be nonzero. -/
theorem generalRoots_correct (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly ≠ 0) :
    AllOutcomes (generalRootsProgram p q t) (RootResult p) := by
  have hz : ¬ (p == 0) = true := by
    intro h
    have he : p = 0 := LawfulBEq.eq_of_beq h
    exact hp (he ▸ CPolynomial.toPoly_zero)
  rw [generalRootsProgram, if_neg hz]
  by_cases hd : p.natDegree = 0
  · rw [if_pos hd]
    change RootResult p (some [],0)
    refine ⟨Nat.zero_le _, ?_⟩
    intro roots hs
    cases hs
    refine ⟨?_, List.nodup_nil, Nat.zero_le _⟩
    intro x
    simp only [List.not_mem_nil, iff_false]
    exact constant_no_roots p hp hd x
  · rw [if_neg hd]
    have hm : (CPolynomial.monicNormalize p).toPoly.Monic := by
      rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
      exact Polynomial.monic_normalize hp
    have hdeg : (0 : WithBot Nat) < (CPolynomial.monicNormalize p).toPoly.degree := by
      rw [normalized_degree, Polynomial.degree_eq_natDegree hp]
      have hn : 0 < p.toPoly.natDegree := by
        rw [CPolynomial.natDegree_toPoly] at hd
        omega
      exact_mod_cast hn
    apply all_mono _ (rootsProgram_correct (CPolynomial.monicNormalize p) q t hq hm hdeg)
    intro out ho
    refine ⟨?_, ?_⟩
    · simpa only [normalized_natDegree] using ho.1
    · intro roots hs
      obtain ⟨hroots,hnodup,hlen⟩ := ho.2 roots hs
      refine ⟨?_, hnodup, ?_⟩
      · intro x
        exact (normalized_roots p x).symm.trans (hroots x)
      · simpa only [normalized_natDegree] using hlen

theorem generalRoots_abort_le (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) (hp : p.toPoly ≠ 0) :
    lazyMean (generalRootsProgram p q t) (fun _ => none)
      (fun v => abortIndicator v.2.1) ≤
        ((p.toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t := by
  have hz : ¬ (p == 0) = true := by
    intro h
    have he : p = 0 := LawfulBEq.eq_of_beq h
    exact hp (he ▸ CPolynomial.toPoly_zero)
  rw [generalRootsProgram, if_neg hz]
  by_cases hd : p.natDegree = 0
  · rw [if_pos hd]
    change (0 : ℚ) ≤ _
    positivity
  · rw [if_neg hd]
    have hm : (CPolynomial.monicNormalize p).toPoly.Monic := by
      rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
      exact Polynomial.monic_normalize hp
    have hdeg : (0 : WithBot Nat) < (CPolynomial.monicNormalize p).toPoly.degree := by
      rw [normalized_degree, Polynomial.degree_eq_natDegree hp]
      have hn : 0 < p.toPoly.natDegree := by
        rw [CPolynomial.natDegree_toPoly] at hd
        omega
      exact_mod_cast hn
    simpa only [normalized_natDegree] using
      rootsProgram_abort_le (CPolynomial.monicNormalize p) q t hq hodd hm hdeg

#print axioms generalRootsProgram
#print axioms normalized_degree
#print axioms normalized_natDegree
#print axioms normalized_roots
#print axioms constant_no_roots
#print axioms generalRoots_correct
#print axioms generalRoots_abort_le
end
end AspisR1.CompPolyGeneralRootsProgram
