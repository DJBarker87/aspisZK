import R0.BadSetBounds

/-! Cardinalities only. This is not the round-by-round state function of §6. -/
set_option autoImplicit false
namespace AspisR0.Opening
open AspisR0.ListsResponses AspisR0.Fold
open Polynomial
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]
attribute [local irreducible] Close Lambda LambdaR

theorem bad_set_cardinalities (D : Data K) (gamma v kappa tau : K) (P : K[X])
    (hp : P.natDegree ≤ 6) :
    (B1 (virtual D)).card ≤ 336869026605739 ∧
    (B2 D).card ≤ 5600 ∧ (B3 D).card ≤ 11200 ∧
    (B4 D gamma v).card ≤ 400 ∧ (B5 D gamma v kappa).card ≤ 200 ∧
    (B6 (channels (batch D gamma))).card ≤ 9396508281246 ∧
    (B7 D gamma kappa tau P).card ≤ 600 :=
  ⟨B1_card _, B2_card D, B3_card D, B4_card D gamma v, B5_card D gamma v kappa,
    B6_card _, B7_card D gamma kappa tau P hp⟩

theorem grouped_cardinalities (D : Data K) (gamma v kappa tau : K) (P : K[X])
    (hp : P.natDegree ≤ 6) :
    (B1 (virtual D) ∪ B2 D ∪ B3 D).card ≤ 336869026605739+16800 ∧
    (B4 D gamma v).card ≤ 400 ∧ (B5 D gamma v kappa).card ≤ 200 ∧
    (B6 (channels (batch D gamma)) ∪ B7 D gamma kappa tau P).card ≤ 9396508281246+600 := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := bad_set_cardinalities D gamma v kappa tau P hp
  refine ⟨?_,h4,h5,?_⟩
  · have ha := Finset.card_union_le (B1 (virtual D)) (B2 D)
    have hb := Finset.card_union_le (B1 (virtual D) ∪ B2 D) (B3 D)
    omega
  · have h := Finset.card_union_le (B6 (channels (batch D gamma))) (B7 D gamma kappa tau P)
    omega

theorem wide_bad_set_cardinalities : type_of% (@bad_set_cardinalities AspisWideTower.WideExact _ _ (Classical.decEq _) _) :=
  @bad_set_cardinalities AspisWideTower.WideExact _ _ (Classical.decEq _) _

#print axioms bad_set_cardinalities
#print axioms grouped_cardinalities
#print axioms wide_bad_set_cardinalities
end
end AspisR0.Opening
