import NNR_Clock
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_ClockFree
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (k k' : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
local notation "env" => DGP_HostDigest.envInst H pda k r
local notation "env'" => DGP_HostDigest.envInst H pda k' r
/-- Hash implementation factors through the SHA reply alone. -/
theorem hashv : LIB_Env.hashv env = LIB_Env.hashv env' := rfl
/-- PDA implementation factors through the PDA reply alone. -/
theorem pda_call : NNH_MRegistryOps.pda env = NNH_MRegistryOps.pda env' := rfl

theorem adapter (base : AdapterRw.Ops) :
 NNH_Tx2SourceConfiguration.adapter base env = NNH_Tx2SourceConfiguration.adapter base env' := by
 unfold NNH_Tx2SourceConfiguration.adapter
 rw [hashv H pda k k' r]

theorem registry (base : AdapterRw.Ops) (D : RSL.DeployedIds) :
 NNH_MRegistryOps.install base D env = NNH_MRegistryOps.install base D env' := by
 unfold NNH_MRegistryOps.install
 rw [pda_call H pda k k' r]

theorem modelSlots (base : AdapterRw.Ops) :
 NNH_Tx2ModelSlots.install base env = NNH_Tx2ModelSlots.install base env' := by
 unfold NNH_Tx2ModelSlots.install
 rw [registry H pda k k' r]

theorem residual (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) :
 NNH_CorrectConfiguration.residual m env = NNH_CorrectConfiguration.residual m env' := by
 unfold NNH_CorrectConfiguration.residual NNH_Tx2SourceConfiguration.fill
 rw [adapter H pda k k' r]

theorem M1b : NFB_NMFBHost.M1b := by
 intro H pda k k' r
 rw [residual H pda k k' r]
 unfold NNH_Tx2Configuration.select
 rw [modelSlots H pda k k' r]
 rfl
#print axioms hashv
#print axioms pda_call
#print axioms adapter
#print axioms registry
#print axioms modelSlots
#print axioms residual
#print axioms M1b
end AspisR1.NNR_ClockFree
end
