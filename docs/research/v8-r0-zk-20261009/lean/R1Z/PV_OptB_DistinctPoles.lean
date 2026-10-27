import R1Z.PV_OptB_PoleCoordinates
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_DistinctPoles
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation R1J.SpendWitnessMap
open PV_OptB_PathPoles
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem distinct_pole_sets (pub : Public M) (w : Wspend) (lam : K) (nonzero : lam ≠ 0) :
    ∃ t u : Fin 16 → M,
      PV_OptB_WitnessFamily.publicInput pub w t = PV_OptB_WitnessFamily.publicInput pub w u ∧
      PoleMassR1.poleSet (trace pub w t) lam ≠ PoleMassR1.poleSet (trace pub w u) lam := by
  have large : Fintype.card (Digest M) * 4096^16 < Fintype.card M ^ 16 := by
    simpa [Digest,R1J.SpendWitnessMap.F,AspisV8R15.ExactTowerBase.M31Exact] using
      PV_OptB_Cardinality.sparse_cardinality
  obtain ⟨t,u,same,different⟩ := PV_OptB_Pigeonhole.distinct_small_sets 16 4096
    (PV_OptB_WitnessFamily.root pub w) (PV_OptB_PoleCoordinates.allowed pub w lam)
    (PV_OptB_PoleCoordinates.contains pub w lam) (PV_OptB_PoleCoordinates.bounded pub w lam nonzero) large
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

/-- A model-level obstruction on a nonempty family of admitted witnesses.
This is NOT a reached-OS-failure counterexample: the public P_R1 check and
emitted body/observer association still have to be carried through. -/
theorem different_noPole (pub : Public M) (w : Wspend) (valid : RspendPlus pub w)
    (lam : K) (nonzero : lam ≠ 0) :
    ∃ t u : Fin 16 → M, ∃ chi : K,
      PV_OptB_WitnessFamily.publicInput pub w t = PV_OptB_WitnessFamily.publicInput pub w u ∧
      (R0Z.HonestValidity.NoPole (trace pub w t) lam chi ↔
        ¬ R0Z.HonestValidity.NoPole (trace pub w u) lam chi) ∧
      RspendPlus (PV_OptB_WitnessFamily.publicInput pub w t) (PV_OptB_WitnessFamily.witness w t) ∧
      RspendPlus (PV_OptB_WitnessFamily.publicInput pub w u) (PV_OptB_WitnessFamily.witness w u) := by
  obtain ⟨t,u,same,different⟩ := distinct_pole_sets pub w lam nonzero
  have point : ∃ chi, ¬ ((chi ∈ PoleMassR1.poleSet (trace pub w t) lam) ↔
      (chi ∈ PoleMassR1.poleSet (trace pub w u) lam)) := by
    by_contra absent
    apply different
    ext chi
    by_contra not_equal
    exact absent ⟨chi,not_equal⟩
  obtain ⟨chi,not_equal⟩ := point
  refine ⟨t,u,chi,same,?_,PV_OptB_WitnessFamily.rspendPlus pub w valid t,
    PV_OptB_WitnessFamily.rspendPlus pub w valid u⟩
  rw [noPole_iff_not_mem,noPole_iff_not_mem]
  tauto

#print axioms distinct_pole_sets
#print axioms noPole_iff_not_mem
#print axioms different_noPole
end R1Z.PV_OptB_DistinctPoles
