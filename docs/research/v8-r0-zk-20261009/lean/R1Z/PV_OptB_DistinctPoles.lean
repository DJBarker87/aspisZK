import R1Z.PV_OptB_PoleCoordinates
import R1Z.PV_OptB_NatCard
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_DistinctPoles
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation R1J.SpendWitnessMap
open PV_OptB_PathPoles
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

attribute [local irreducible] PV_OptB_PathPoles.trace PV_OptB_WitnessFamily.root
  PV_OptB_WitnessFamily.publicInput PV_OptB_PoleCoordinates.allowed

theorem distinct_pole_sets (pub : Public M) (w : Wspend) (lam : K) (nonzero : lam ≠ 0) :
    ∃ t u : Fin 16 → M,
      PV_OptB_WitnessFamily.publicInput pub w t = PV_OptB_WitnessFamily.publicInput pub w u ∧
      PoleMassR1.poleSet (trace pub w t) lam ≠ PoleMassR1.poleSet (trace pub w u) lam := by
  have bounded := PV_OptB_PoleCoordinates.bounded pub w lam nonzero
  have contains := PV_OptB_PoleCoordinates.contains pub w lam
  obtain ⟨t,u,same,different⟩ := @PV_OptB_NatCard.distinct_small_sets M (Digest M)
    inferInstance inferInstance 16 4096
    (PV_OptB_WitnessFamily.root pub w) (PV_OptB_PoleCoordinates.allowed pub w lam)
    contains bounded (PV_OptB_NatCard.large_for (by
      change Nat.card (ZMod AspisV8R15.ExactTowerBase.P) = 2147483647
      exact Nat.card_zmod _))
  refine ⟨t,u,PV_OptB_WitnessFamily.public_eq_of_root_eq pub w t u same,?_⟩
  intro equal
  exact different (PV_OptB_PoleCoordinates.equal_of_poleSet_equal pub w lam t u equal)

theorem noPole_iff_not_mem (A : Trace K) (lam chi : K) :
    R0Z.HonestValidity.NoPole A lam chi ↔ chi ∉ PoleMassR1.poleSet A lam := by
  constructor
  · intro clear member
    unfold PoleMassR1.poleSet at member
    obtain ⟨p,hp,value⟩ := Finset.mem_image.mp member
    have active : CopyActiveRow p.1 := by
      have row := (Finset.mem_product.mp hp).1
      unfold PoleMassR1.activeRows at row
      exact (Finset.mem_filter.mp row).2
    have values := clear p.1 active p.2.1
    cases side : p.2.2
    · exact values.2 (by simpa only [PoleMassR1.poleValue,side,cond_false] using value.symm)
    · exact values.1 (by simpa only [PoleMassR1.poleValue,side,cond_true] using value.symm)
  · intro absent
    by_contra not_clear
    exact absent (PoleMassR1.mem_poleSet_of_not_noPole A lam chi not_clear)

#print axioms distinct_pole_sets
#print axioms noPole_iff_not_mem
end R1Z.PV_OptB_DistinctPoles
