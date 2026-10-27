import R1Z.PV_Inv_PoleMass
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_PoleUnion
open R0Z.JointView R0P R0Z.FsAbort R0Z.FsGood R0Z.FsStatement R0Z.HvzkV
open PoleMassR1 PV_Inv_PoleMass
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem eight_attempts {C : Type} [Fintype C] (draw : Fin 8 → C → Challenges K) (Q : ℕ)
    (law : ∀ i, Sem1Uniform (draw i) Q) (t : Trace K) :
    eventMass (fun c => ∃ i, zeroEvent t ((draw i c).sem 0) ((draw i c).sem 1)) ≤
      8 * ((4096 : ℚ)/Q) := by
  have h := R0Z.FsAbortBounds.mass_exists_le_card
    (fun i c => zeroEvent t ((draw i c).sem 0) ((draw i c).sem 1)) ((4096 : ℚ)/Q)
    (fun i => PV_Inv_PoleMass.mass (draw i) Q (law i) t)
  simpa only [eventMass,R0Z.FsAbortBounds.mass,Fintype.card_fin,Nat.cast_ofNat] using h

#print axioms eight_attempts
end R1Z.PV_Inv_PoleUnion
