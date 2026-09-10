import OwnSymbolCollision

/-! Complete fibres are counted on the tuple's own componentwise support,
not on the larger support of one sampled scalar-power batch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 120000

namespace AspisV8.OwnFibreGeometry
open Finset
noncomputable section
variable {F I : Type*} [DecidableEq F] [DecidableEq I]

def common (U : Finset F) (emb : F × Fin 4 ↪ I) (own : Finset I) : Finset F := by
  classical
  exact U.filter fun f => ∀ slot, emb (f, slot) ∈ own

theorem common_subset (U : Finset F) (emb : F × Fin 4 ↪ I) (own : Finset I) :
    common U emb own ⊆ U := Finset.filter_subset _ _

theorem common_card (U : Finset F) (emb : F × Fin 4 ↪ I) (own : Finset I) :
    4 * (common U emb own).card ≤ own.card := by
  classical
  have subset : ((common U emb own) ×ˢ (Finset.univ : Finset (Fin 4))).map emb ⊆ own := by
    intro i member
    obtain ⟨pair, present, equal⟩ := Finset.mem_map.mp member
    obtain ⟨inCommon, slotMember⟩ := Finset.mem_product.mp present
    rw [← equal]
    exact (Finset.mem_filter.mp inCommon).2 pair.2
  have bound := Finset.card_le_card subset
  simpa only [Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Nat.mul_comm] using bound

theorem insufficient_own_common_cap (U : Finset F) (emb : F × Fin 4 ↪ I)
    (own : Finset I) (insufficient : own.card < 38228) :
    (common U emb own).card ≤ 9556 := by
  have bound := common_card U emb own
  omega

theorem common_residual_iff {K : Type*} [Field K]
    (U : Finset F) (Symbols : Finset I) (emb : F × Fin 4 ↪ I)
    (received expected : Fin 29 → I → K)
    (inside : ∀ f ∈ U, ∀ slot, emb (f, slot) ∈ Symbols)
    (f : F) (member : f ∈ U) :
    f ∈ common U emb (OwnSymbolCollision.own Symbols received expected) ↔
      ∀ slot, OwnSymbolCollision.residual received expected (emb (f, slot)) = 0 := by
  classical
  constructor
  · intro inCommon slot
    exact (OwnSymbolCollision.residual_zero_iff _ _ _).mpr
      (Finset.mem_filter.mp ((Finset.mem_filter.mp inCommon).2 slot)).2
  · intro zeros
    apply Finset.mem_filter.mpr
    refine ⟨member, fun slot => Finset.mem_filter.mpr ⟨inside f member slot, ?_⟩⟩
    exact (OwnSymbolCollision.residual_zero_iff _ _ _).mp (zeros slot)

#print axioms common_subset
#print axioms common_card
#print axioms insufficient_own_common_cap
#print axioms common_residual_iff
end
end AspisV8.OwnFibreGeometry
