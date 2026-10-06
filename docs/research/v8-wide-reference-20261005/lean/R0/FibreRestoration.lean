import R0.ListsResponses
import R0.Round

/-! Step 6: a matched final response restores all four symbols of every
matched fibre, with the exact 4|M| count. -/
set_option autoImplicit false
namespace AspisR0.FibreRestoration
open AspisR0.ListsResponses AspisR0.Fold AspisR0.RoundNormalization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisV5ComponentCConcreteFoldLinearity AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement AspisV5FriCoherentCandidateExtraction
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def join (t : Fin 4 → FinalMessage K) : InitialMessage K :=
  fun i => t ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩ ⟨i.val / 4,by omega⟩

theorem lane_join (t : Fin 4 → FinalMessage K) (s : Fin 4) : coefficientLane 256 s (join t) = t s := by
  funext d
  change t ⟨(4*d.val+s.val)%4, _⟩ ⟨(4*d.val+s.val)/4, _⟩ = t s d
  have hs : (⟨(4*d.val+s.val)%4, by omega⟩ : Fin 4) = s := by apply Fin.ext; dsimp; omega
  have hd : (⟨(4*d.val+s.val)/4, by omega⟩ : Fin 256) = d := by apply Fin.ext; dsimp; omega
  rw [hs, hd]

theorem fold_join (t : Fin 4 → FinalMessage K) (alpha : K) :
    foldMessage alpha (join t) = exactFinalMessageCurve t alpha := by
  funext d
  rw [foldMessage_eq_sum]
  simp only [exactFinalMessageCurve, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  have h := congrFun (lane_join t s) d
  change join t (childIndex d s) = t s d at h
  rw [h]
  ring

def fibreSet (M : Finset (Fin 262144)) : Finset (Fin 1048576) :=
  (M.product Finset.univ).image (fun p => childIndex p.1 p.2)

theorem child_injective : Function.Injective (fun p : Fin 262144 × Fin 4 => childIndex p.1 p.2) := by
  intro p q h
  have he := congrArg Fin.val h
  simp only [childIndex_val] at he
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem fibreSet_card (M : Finset (Fin 262144)) : (fibreSet M).card = 4*M.card := by
  rw [fibreSet, Finset.card_image_of_injective _ child_injective]
  calc
    _ = M.card * (Finset.univ : Finset (Fin 4)).card := Finset.card_product M Finset.univ
    _ = _ := by simp [Nat.mul_comm]

theorem restore (R : InitialWord K) (t : Fin 4 → FinalMessage K) (M : Finset (Fin 262144))
    (hs : M ⊆ jointAgreementSet exactFinalEncoder (channels R) t) :
    ∀ i ∈ fibreSet M, R i = exactInitialEncoder (join t) i := by
  intro i hi
  obtain ⟨⟨u,s⟩,hmem,rfl⟩ := Finset.mem_image.mp hi
  have hu := (Finset.mem_product.mp hmem).1
  have hc := hs hu
  simp only [jointAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  have decoded : fibreTransform u (fibre R u) = fibreTransform u (fibre (exactInitialEncoder (join t)) u) := by
    funext j
    change channels R j u = channels (exactInitialEncoder (join t)) j u
    rw [encoded_channels, lane_join]
    exact hc j
  have same : fibre R u = fibre (exactInitialEncoder (join t)) u :=
    (fibre_inverse u).2.injective decoded
  simpa only [fibre] using congrFun same s

theorem matched_close (R : InitialWord K) (alpha : K) (F : FinalMessage K)
    (M : Finset (Fin 262144)) (large : 9558 ≤ M.card)
    (matched : ∃ t : Fin 4 → FinalMessage K,
      M ⊆ jointAgreementSet exactFinalEncoder (channels R) t ∧ F = exactFinalMessageCurve t alpha) :
    ∃ q ∈ Close R, F = foldMessage alpha q := by
  obtain ⟨t, hs, hF⟩ := matched
  refine ⟨join t, ?_, hF.trans (fold_join t alpha).symm⟩
  rw [mem_Close]
  have subset : fibreSet M ⊆ agreementSet R (exactInitialEncoder (join t)) := by
    intro i hi
    simp only [agreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact restore R t M hs i hi
  have hc := Finset.card_le_card subset
  rw [fibreSet_card] at hc
  omega

#print axioms restore
#print axioms fibreSet_card
#print axioms matched_close
end
end AspisR0.FibreRestoration
