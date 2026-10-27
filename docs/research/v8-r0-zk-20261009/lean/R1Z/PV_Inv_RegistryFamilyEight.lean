import R1Z.PV_Inv_RegistryFamilyMass
import R0Z.FsAbortBounds
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_RegistryFamilyEight
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV PoleMassR1
variable {K W C : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [Zero W] [DecidableEq W] [Fintype C]

theorem eight_attempts (t : Trace K) (draw : Fin 8 → C → Challenges K) (Q : Nat)
    (law : ∀ k, Sem1Uniform (draw k) Q) :
    eventMass (fun c => ∃ k, PV_Inv_RegistryFamilyEvent.event (W := W) t ((draw k c).sem 0) ((draw k c).sem 1)) ≤
      8 * ((4096 : ℚ)/Q) := by
  have h := R0Z.FsAbortBounds.mass_exists_le_card
    (fun k c => PV_Inv_RegistryFamilyEvent.event (W := W) t ((draw k c).sem 0) ((draw k c).sem 1)) ((4096 : ℚ)/Q)
    (fun k => PV_Inv_RegistryFamilyMass.one_attempt t (draw k) Q (law k))
  simpa only [eventMass,R0Z.FsAbortBounds.mass,Fintype.card_fin,Nat.cast_ofNat] using h

#print axioms eight_attempts
end R1Z.PV_Inv_RegistryFamilyEight
