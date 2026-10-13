import R1ConcreteProjection
import R1FinalResponses

/-! Transfer the existing exact 256-coefficient matched-response theorem to
the concrete 64-coefficient log-16 encoder by repeating each received word
four times. No new decoder/certificate premise is introduced. This is an
encoder-level statement; runtime channel recovery and FS remain separate. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.SecondFoldMatched

open scoped BigOperators
open AspisCircleGroupOrder
open AspisR1.ConcreteProjection
open AspisR1.FinalResponses
open AspisWide.FinalEncoder AspisWide.Agreement
open AspisV5FriDegreeThreeCorrelatedAgreement

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

/-- Repeat a parent word on all four children. -/
def repeatedWord (w : SmallWord K) : Fin 262144 → K :=
  fun k => w (AspisR1.parentIndex k)

/-- The existing existential unmatched-response bad set of the lifted words. -/
def secondBad (g : Fin 4 → SmallWord K) : Finset K :=
  B6 (fun s => repeatedWord (g s))

theorem secondBad_card (g : Fin 4 → SmallWord K) :
    (secondBad g).card ≤ 9396508281246 :=
  B6_card _

private theorem child_mem_fullQuartetSet
    (S : Finset (Fin 65536)) (i : Fin 65536) (hi : i ∈ S) (s : Fin 4) :
    AspisR1.childIndex i s ∈ AspisR1.fullQuartetSet S := by
  simp only [AspisR1.fullQuartetSet, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨i, hi, s, rfl⟩

/-- Outside the unchanged exact-final bad set, every sufficiently supported
64-coefficient response has a matching four-component decomposition. -/
theorem second_match
    (g : Fin 4 → SmallWord K) (alpha : K)
    (hgood : alpha ∉ secondBad g)
    (f : SmallMessage K) (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hvalid : ∀ i ∈ S, curveValue g alpha i = secondEncoder f i) :
    ∃ b : Fin 4 → SmallMessage K,
      (∀ i ∈ S, ∀ s : Fin 4, g s i = secondEncoder (b s) i) ∧
      f = ∑ s : Fin 4, alpha ^ s.val • b s := by
  let lifted := fun s : Fin 4 => repeatedWord (g s)
  let response : FinalResponse K :=
    (AspisR1.sparseLift f, AspisR1.fullQuartetSet S)
  have hv : AlphaValid lifted alpha response := by
    constructor
    · change 9557 < (AspisR1.fullQuartetSet S).card
      rw [AspisR1.fullQuartetSet_card]
      omega
    · intro k hk
      change k ∈ AspisR1.fullQuartetSet S at hk
      have hi := AspisR1.parentIndex_mem_of_mem_fullQuartetSet S hk
      change curveValue lifted alpha k = exactFinalEncoder (AspisR1.sparseLift f) k
      rw [← AspisR1.childIndex_parentIndex_slotIndex (n := 65536) k,
        exactFinal_sparseLift_child]
      simpa only [curveValue, lifted, repeatedWord,
        AspisR1.parentIndex_childIndex] using hvalid (AspisR1.parentIndex k) hi
  obtain ⟨a, hsupport, hcurve⟩ := alpha_match lifted alpha hgood response hv
  have hfour (s : Fin 4) (i : Fin 65536) (hi : i ∈ S) (j : Fin 4) :
      exactFinalEncoder (a s) (AspisR1.childIndex i j) = g s i := by
    have hk := hsupport (child_mem_fullQuartetSet S i hi j)
    have hx := (Finset.mem_filter.mp hk).2 s
    change repeatedWord (g s) (AspisR1.childIndex i j) =
      exactFinalEncoder (a s) (AspisR1.childIndex i j) at hx
    simpa only [repeatedWord, AspisR1.parentIndex_childIndex] using hx.symm
  let b := fun s : Fin 4 => AspisR1.laneCoefficients 64 0 (a s)
  refine ⟨b, ?_, ?_⟩
  · intro i hi s
    exact (secondEncoder_of_repeated_match S (by omega) (a s) (g s)
      (hfour s) i hi).symm
  · funext d
    have h := congrFun hcurve (AspisR1.childIndex d 0)
    simpa [response, AspisR1.sparseLift, exactFinalMessageCurve,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b,
      AspisR1.laneCoefficients] using h

#print axioms secondBad_card
#print axioms second_match
end AspisR1.SecondFoldMatched
end
