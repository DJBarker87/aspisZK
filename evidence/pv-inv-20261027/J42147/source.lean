import R1Z.PV_Inv_BadContainment
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_PoleMass
open R0Z.JointView R0P R0Z.HonestValidity R0Z.FsAbort R0Z.FsGood R0Z.FsStatement R0Z.HvzkV
open PV_Inv_Pack PV_Inv_ModelRow PV_Inv_PackOperands PoleMassR1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Existentially ranges over both side packs, every active row, every weight,
and every reached operand, so no union bound is charged per invocation. -/
def zeroEvent (t : Trace K) (lam chi : K) : Prop :=
  ∃ b : Fin 1024, CopyActiveRow b ∧ ∃ weights : Fin 2 → K, ∃ s : Slots K,
   (PV_Inv_PackList.run PV_Inv_Pack.empty (entries t lam b CopyLink.producer weights)=some s ∨
    PV_Inv_PackList.run PV_Inv_Pack.empty (entries t lam b CopyLink.consumer weights)=some s) ∧
    0 ∈ operands chi s

theorem contained (t : Trace K) (lam chi : K) (hz : zeroEvent t lam chi) : ¬ NoPole t lam chi := by
  obtain ⟨b,hb,w,s,hr,hz⟩ := hz
  rcases hr with hp|hc
  · exact PV_Inv_BadContainment.producer_zero_is_pole t lam chi b hb w s hp hz
  · exact PV_Inv_BadContainment.consumer_zero_is_pole t lam chi b hb w s hc hz

theorem mass {C : Type} [Fintype C] (draw : C → Challenges K) (Q : ℕ)
    (law : Sem1Uniform draw Q) (t : Trace K) :
    eventMass (fun c => zeroEvent t ((draw c).sem 0) ((draw c).sem 1)) ≤ (4096 : ℚ)/Q := by
  exact (eventMass_mono _ _ (fun c h => contained t _ _ h)).trans (pole_mass_le draw Q law t)

#print axioms contained
#print axioms mass
end R1Z.PV_Inv_PoleMass
