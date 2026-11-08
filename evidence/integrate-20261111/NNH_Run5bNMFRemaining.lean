import NNH_Run5bNMF
import NFB_NMFB
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bNMFRemaining
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Libraries NNH_Run5bNMF
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
/-- The NFB Remaining obligation, reindexed at the corrected signature.
The old NFB_NMFBHost.Remaining is deliberately not asserted. -/
abbrev Remaining (I0 : RSL.TAS.Impl L V0 VL) : Prop :=
 RSL.NFB.Remaining (S (Tx := Tx) L0 copy std) L D V0 VL P C (NNH_064Install.install I0)
 (NNH_G1aEnv.field (NNH_Run5bHost.S_host (Tx := Tx) L0 copy std) I0)
 (recSig (Tx := Tx) L0 copy std)
theorem remaining (I0 : RSL.TAS.Impl L V0 VL) : Remaining (Tx := Tx) L0 copy std I0 :=
 (nmfB (Tx := Tx) L0 copy std I0).root0_or_rec
#print axioms remaining
end AspisR1.NNH_Run5bNMFRemaining
end
