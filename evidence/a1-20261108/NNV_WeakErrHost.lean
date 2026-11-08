import NNH_Run5bHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_WeakErrHost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_ReturnedCheckpoint NNH_Run5bCtx
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
/-- Exact corrected-host interface, with the approved weak Err clause.
This is statement normalization only, not a producer of the A1 field. -/
theorem modelRet1 (c : Ctx W Tx) (a : RSL.TX1_345.Args) (r : Except RSL.ProgramError RSL.Bytes) :
 (NNH_Run5bHost.S_host L0 copy std).ModelRet1 c a r ↔
 ∀ e p data,
 a = NNE_PhysicalAccepted.child1 NND_Carrier.error e p data →
 (∀ saved, r = .ok (nativeBytes saved) → model1 c p e.first data = .ok (.Ok saved)) ∧
 (∀ error, r = .error error → ¬ ∃ saved, model1 c p e.first data = .ok (.Ok saved)) := Iff.rfl
#print axioms modelRet1
end AspisR1.NNV_WeakErrHost
end
