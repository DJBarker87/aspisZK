import R1Z.PV_Inv_RegistryFamilyEight
import R1Z.ReadBudgetR1
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_HeadlineCharge
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV PoleMassR1
variable {K W C : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [Zero W] [DecidableEq W] [Fintype C]

/-- This is exactly PrivacyR1Final.modelError's final summand. This numerical
fact is not, by itself, a proof of native event membership in poleBad. -/
def existingPoleCharge : ℚ := (8 : ℚ) * (4096 / (((2^31-1)^4-1 : Nat) : ℚ))

theorem mass_at_existing_term (t : Trace K) (draw : Fin 8 → C → Challenges K)
    (law : ∀ k, Sem1Uniform (draw k) ((2^31-1)^4-1)) :
    eventMass (fun c => ∃ k, PV_Inv_RegistryFamilyEvent.event (W := W) t ((draw k c).sem 0) ((draw k c).sem 1)) ≤
      existingPoleCharge :=
  PV_Inv_RegistryFamilyEight.eight_attempts t draw _ law

theorem numerical_term : existingPoleCharge ≤ 1 / 2^109 + 1 / 2^138 + 1 / 2^160 :=
  ReadBudgetR1.pole_N8

#print axioms mass_at_existing_term
#print axioms numerical_term
end R1Z.PV_Inv_HeadlineCharge
