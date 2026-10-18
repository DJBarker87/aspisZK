import SequentialProgramInvariants
import CompPolyFactorOracleProgram
import CompPolyFactorCertificate

noncomputable section
namespace AspisR1.CompPolySequentialFactorInvariant
open CompPoly Polynomial AspisR1.CompPolyFactorCertificate
open AspisR1.CompPolyFactorOracleProgram AspisR1.CompPolySplitRetries
open AspisR1.CompPolySplitFactorQuality
open AspisR1.SequentialFreshProgram AspisR1.SequentialProgramInvariants
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def FactorResult (f : CPolynomial K) (cursor : Nat) (out : Option (List K) × Nat) : Prop :=
  out.2 ≤ cursor + (f.toPoly.natDegree-1) ∧
    ∀ roots, out.1 = some roots → linearProduct roots = f.toPoly

/-- Both the unconditional query budget and the conditional certificate hold
on every branch of the same sequential, fresh-answer factorizer. -/
theorem sequential_factor_invariant (q t fuel node cursor : Nat) (f : CPolynomial K)
    (hf : f.toPoly.Monic) :
    AllOutcomes (sequential (factorProgram q t fuel node f) cursor)
      (FactorResult f cursor) := by
  induction fuel generalizing node cursor f with
  | zero =>
    change FactorResult f cursor (none,cursor)
    constructor
    · dsimp only
      omega
    · intro roots hs
      contradiction
  | succ fuel ih =>
    rw [factorProgram]
    split
    · rename_i hzero
      change FactorResult f cursor (some [],cursor)
      refine ⟨by dsimp only; omega, ?_⟩
      intro roots hs
      cases hs
      have hn : f.toPoly.natDegree = 0 := (CPolynomial.natDegree_toPoly f).symm.trans hzero
      simpa only [linearProduct, List.map_nil, List.prod_nil] using
        (hf.natDegree_eq_zero.mp hn).symm
    · split
      · rename_i hone
        change FactorResult f cursor (some [-f.coeff 0],cursor)
        refine ⟨by dsimp only; omega, ?_⟩
        intro roots hs
        cases hs
        have hn : f.toPoly.natDegree = 1 := (CPolynomial.natDegree_toPoly f).symm.trans hone
        simpa only [linearProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, C_neg, sub_neg_eq_add, CPolynomial.coeff_toPoly] using
          (hf.eq_X_add_C hn).symm
      · rename_i hzero hone
        change ∀ tape, AllOutcomes (sequential _ (cursor+1)) (FactorResult f cursor)
        intro tape
        have hn : 2 ≤ f.toPoly.natDegree := by
          rw [CPolynomial.natDegree_toPoly] at hzero hone
          omega
        cases hd : retry f q t tape with
        | none =>
          change FactorResult f cursor (none,cursor+1)
          refine ⟨by dsimp only; omega, ?_⟩
          intro roots hs
          contradiction
        | some d =>
          have hquality := retry_quality f d q t tape hf hd
          have hc := complement_quality f d hf hquality.1 hquality.2
          dsimp only at hc
          have hsum : d.toPoly.natDegree + (f.divByMonic d).toPoly.natDegree =
              f.toPoly.natDegree := by
            rw [← natDegree_mul hquality.1.ne_zero hc.2.1.ne_zero, hc.1]
          rw [sequential_bind]
          apply all_bind
          apply all_mono _ (ih (2*node+1) (cursor+1) d hquality.1)
          intro left hleft
          rcases left with ⟨left,lc⟩
          rcases hleft with ⟨hlbound,hlcert⟩
          cases left with
          | none =>
            change FactorResult f cursor (none,lc)
            refine ⟨by dsimp only at *; omega, ?_⟩
            intro roots hs
            contradiction
          | some l =>
            rw [sequential_bind]
            apply all_bind
            apply all_mono _ (ih (2*node+2) lc (f.divByMonic d) hc.2.1)
            intro right hright
            rcases right with ⟨right,rc⟩
            rcases hright with ⟨hrbound,hrcert⟩
            cases right with
            | none =>
              change FactorResult f cursor (none,rc)
              refine ⟨by dsimp only at *; omega, ?_⟩
              intro roots hs
              contradiction
            | some r =>
              change FactorResult f cursor (some (l++r),rc)
              refine ⟨by dsimp only at *; omega, ?_⟩
              intro roots hs
              cases hs
              rw [linearProduct, List.map_append, List.prod_append]
              change linearProduct l * linearProduct r = f.toPoly
              rw [hlcert l rfl, hrcert r rfl]
              exact hc.1

theorem sequential_factor_eval (q t fuel node cursor : Nat) (f : CPolynomial K)
    (hf : f.toPoly.Monic) (H : Nat → Fin t → K × K) :
    FactorResult f cursor (eval H (sequential (factorProgram q t fuel node f) cursor)).2 :=
  all_eval H _ _ (sequential_factor_invariant q t fuel node cursor f hf)

#print axioms FactorResult
#print axioms sequential_factor_invariant
#print axioms sequential_factor_eval
end AspisR1.CompPolySequentialFactorInvariant
