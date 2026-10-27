import R1Z.PV_Inv_RegistryFamilyEvent
import R1Z.PoleMassR1
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_RegistryFamilyMass
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV PoleMassR1
variable {K W C : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [Zero W] [DecidableEq W] [Fintype C]

theorem one_attempt (t : Trace K) (draw : C → Challenges K) (Q : Nat) (law : Sem1Uniform draw Q) :
    eventMass (fun c => PV_Inv_RegistryFamilyEvent.event (W := W) t ((draw c).sem 0) ((draw c).sem 1)) ≤
      (4096 : ℚ)/Q := by
  exact (eventMass_mono _ _ (fun _ hz => PV_Inv_RegistryFamilyEvent.contained t _ _ hz)).trans
    (pole_mass_le draw Q law t)

#print axioms one_attempt
end R1Z.PV_Inv_RegistryFamilyMass
