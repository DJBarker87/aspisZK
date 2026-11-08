import NNH_Run5bHost
import NNR_RecorderClockFree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bClock
open Aeneas Aeneas.Std S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Run5bCtx NNH_Run5bHost
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem environment (c : Ctx W Tx) :
 (S_host L0 copy std).env2 c = NFB_NMFBHost.env2 c := rfl
theorem represented (c : Ctx W Tx) :
 (S_host L0 copy std).EnvRep c (NFB_NMFBHost.env2 c) :=
 NNR_Clock.M1c c
/-- The old M1 disagreement is impossible at the corrected signature. -/
theorem no_disagreement (c : Ctx W Tx) :
 ¬ NNH_HostWeak241.clock ((S_host L0 copy std).env2 c) ≠ c.j.slot :=
 fun h => h (NNR_Clock.M1a c)
/-- Both correction and representation are total on the existing carrier. -/
theorem total_representation (c : Ctx W Tx) :
 (S_host L0 copy std).Exhibited c ∧
 (S_host L0 copy std).EnvRep c ((S_host L0 copy std).env2 c) :=
 ⟨rfl,NNR_Clock.M1c c⟩
#print axioms environment
#print axioms represented
#print axioms no_disagreement
#print axioms total_representation
end AspisR1.NNH_Run5bClock
end
