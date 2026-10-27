import R1Z.PV_OptB_DistinctPoles
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_DifferentNoPole
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation R1J.SpendWitnessMap
open PV_OptB_PathPoles PV_OptB_DistinctPoles
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
attribute [local irreducible] PV_OptB_PathPoles.trace PV_OptB_WitnessFamily.publicInput PV_OptB_WitnessFamily.witness
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

#print axioms different_noPole
end R1Z.PV_OptB_DifferentNoPole
