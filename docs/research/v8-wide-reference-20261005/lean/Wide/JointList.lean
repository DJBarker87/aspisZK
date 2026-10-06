import Wide.BatchSeparation
import Wide.MultiplicityThreeGS
import Wide.EncoderLinearity
import WideTower

/-! Joint width-29 list bound, derived from the single-word theorem
`exactInitialCloseCandidate_card_lt_101` by separating 101 tuples with one
nonzero batching challenge. -/
set_option autoImplicit false
namespace AspisWide.JointList
open AspisV6Width29CorrelatedAgreement
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.Agreement
open AspisWide.MultiplicityThreeGS AspisWide.BatchSeparation

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem initialMessageCurve_eq_batch (components : Fin 29 → InitialMessage K) (z : K) :
    exactInitialMessageCurve components z = width29CurveValue components z := by
  funext x
  simp only [exactInitialMessageCurve_apply, width29CurveValue, width29Batch]

/-- Each tuple consists of 29 released messages, hence 29 exact codewords.
Injectivity of the encoder makes this also the bound on distinct codeword tuples. -/
theorem jointInitialList_card_le_100
    (lanes : Fin 29 → InitialWord K)
    (family : Finset (Fin 29 → InitialMessage K))
    (close : ∀ components ∈ family,
      38230 ≤ (width29JointAgreementSet exactInitialEncoder lanes components).card) :
    family.card ≤ 100 := by
  classical
  by_contra tooMany
  obtain ⟨small, subset, size⟩ := Finset.exists_subset_card_eq
    (show 101 ≤ family.card by omega)
  have baseCard : AspisCircleGroupOrder.P ≤ Fintype.card K := by
    simpa only [ZMod.card] using
      Fintype.card_le_of_injective (algebraMap (ZMod AspisCircleGroupOrder.P) K)
        (FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K)
  have pairBudget : small.card.choose 2 * 28 = 141400 := by
    rw [size, Nat.choose_two_right]
  have room : small.card.choose 2 * 28 < Fintype.card K - 1 := by
    rw [pairBudget]
    have primeSize : 141401 < AspisCircleGroupOrder.P := by
      norm_num [AspisCircleGroupOrder.P]
    omega
  obtain ⟨z, _nonzero, separates⟩ := exists_nonzero_injective_batch small room
  let received : InitialWord K := width29CurveValue lanes z
  let candidate : small → ExactInitialCloseCandidate received := fun t =>
    ⟨exactInitialMessageCurve t.1 z, by
      have supports : width29JointAgreementSet exactInitialEncoder lanes t.1 ⊆
          AspisV5FriCoherentCandidateExtraction.agreementSet received
            (exactInitialEncoder (exactInitialMessageCurve t.1 z)) := by
        intro x hx
        simp only [width29JointAgreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and] at hx
        simp only [AspisV5FriCoherentCandidateExtraction.agreementSet,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [exactInitialEncoder_messageCurve]
        change width29Batch (fun i => lanes i x) z =
          width29Batch (fun i => exactInitialEncoder (t.1 i) x) z
        congr 1
        funext i
        exact hx i
      exact (close t.1 (subset t.2)).trans (Finset.card_le_card supports)⟩
  have injective : Function.Injective candidate := by
    intro left right equal
    apply Subtype.ext
    apply separates left.2 right.2
    have messages := congrArg Subtype.val equal
    change exactInitialMessageCurve left.1 z = exactInitialMessageCurve right.1 z at messages
    simpa only [initialMessageCurve_eq_batch] using messages
  letI : Fintype (ExactInitialCloseCandidate received) := Fintype.ofFinite _
  have count := Fintype.card_le_of_injective candidate injective
  have singleWordCap := exactInitialCloseCandidate_card_lt_101 received
  rw [Nat.card_eq_fintype_card] at singleWordCap
  rw [Fintype.card_coe, size] at count
  omega

theorem wideJointInitialList_card_le_100
    (lanes : Fin 29 → InitialWord AspisWideTower.WideExact)
    (family : Finset (Fin 29 → InitialMessage AspisWideTower.WideExact))
    (close : ∀ components ∈ family,
      38230 ≤ (width29JointAgreementSet exactInitialEncoder lanes components).card) :
    family.card ≤ 100 := by
  classical
  exact jointInitialList_card_le_100 lanes family close

/-- Literal codeword-tuple form: each of the 29 coordinates is in the exact
encoder image, and the 29 agreements must hold on the same 38230 points. -/
theorem jointInitialCodewords_card_le_100
    (lanes : Fin 29 → InitialWord K)
    (family : Finset (Fin 29 → InitialWord K))
    (codewords : ∀ words ∈ family, ∀ i,
      ∃ message : InitialMessage K, exactInitialEncoder message = words i)
    (close : ∀ words ∈ family,
      38230 ≤ (Finset.univ.filter fun x => ∀ i, lanes i x = words i x).card) :
    family.card ≤ 100 := by
  classical
  let selected : family → Fin 29 → InitialMessage K := fun t i =>
    Classical.choose (codewords t.1 t.2 i)
  have encoded : ∀ t : family, ∀ i, exactInitialEncoder (selected t i) = t.1 i := by
    intro t i
    exact Classical.choose_spec (codewords t.1 t.2 i)
  have injective : Function.Injective selected := by
    intro left right equal
    apply Subtype.ext
    funext i
    rw [← encoded left i, ← encoded right i]
    exact congrArg exactInitialEncoder (congrFun equal i)
  let messages := Finset.univ.image selected
  have size : messages.card = family.card := by
    rw [Finset.card_image_of_injective _ injective, Finset.card_univ, Fintype.card_coe]
  rw [← size]
  apply jointInitialList_card_le_100 lanes messages
  intro components member
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp member
  have jointEq : width29JointAgreementSet exactInitialEncoder lanes (selected t) =
      Finset.univ.filter (fun x => ∀ i, lanes i x = t.1 i x) := by
    simp only [width29JointAgreementSet, encoded]
  rw [jointEq]
  exact close t.1 t.2

theorem wideJointInitialCodewords_card_le_100
    (lanes : Fin 29 → InitialWord AspisWideTower.WideExact)
    (family : Finset (Fin 29 → InitialWord AspisWideTower.WideExact))
    (codewords : ∀ words ∈ family, ∀ i,
      ∃ message : InitialMessage AspisWideTower.WideExact,
        exactInitialEncoder message = words i)
    (close : ∀ words ∈ family,
      38230 ≤ (Finset.univ.filter fun x => ∀ i, lanes i x = words i x).card) :
    family.card ≤ 100 := by
  classical
  exact jointInitialCodewords_card_le_100 lanes family codewords close

#print axioms jointInitialCodewords_card_le_100
#print axioms wideJointInitialCodewords_card_le_100
#print axioms initialMessageCurve_eq_batch
#print axioms jointInitialList_card_le_100
#print axioms wideJointInitialList_card_le_100
end AspisWide.JointList
