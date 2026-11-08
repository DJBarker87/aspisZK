import NFB_BinderGroup
import NNH_HostExec
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_BinderHost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_HostCtx NNH_LiteralHost
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

def before : RSL.TAS.Sig :=
 NNH_RecordSig.physical (envSig (Tx := Tx) L0 copy) (data L0 copy std) (record L0 copy)

theorem host_shape : S_host (Tx := Tx) L0 copy std =
 RSL.NFB.withRetained (before L0 copy std) (retained L0) := rfl

/-- The grouped theorem terms specialized to the real unretained host. -/
abbrev exec_same := @RSL.NFB.exec_same (before (Tx := Tx) L0 copy std) (retained L0)
abbrev top_splitB_grouped := @RSL.NFB.top_splitB_grouped (before (Tx := Tx) L0 copy std) (retained L0)
abbrev deployed_charge_grouped := @RSL.NFB.deployed_charge_grouped (before (Tx := Tx) L0 copy std) (retained L0)
abbrev failG_eq := @RSL.NFB.failG_eq (before (Tx := Tx) L0 copy std) (retained L0)
abbrev indicator_eq_of_fixed := @RSL.NFB.indicator_eq_of_fixed (before (Tx := Tx) L0 copy std) (retained L0)
abbrev indicator_eq_of_trust := @RSL.NFB.indicator_eq_of_trust (before (Tx := Tx) L0 copy std) (retained L0)
#print axioms host_shape
#print axioms exec_same
#print axioms top_splitB_grouped
#print axioms deployed_charge_grouped
#print axioms failG_eq
#print axioms indicator_eq_of_fixed
#print axioms indicator_eq_of_trust
end AspisR1.NNR_BinderHost
end
