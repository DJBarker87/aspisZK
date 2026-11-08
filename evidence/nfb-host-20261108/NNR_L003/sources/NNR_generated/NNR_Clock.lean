import NFB_NMFBHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_Clock
open Aeneas Aeneas.Std Result NNH_HostCtx
open S2W_D189Wrappers

theorem roundtrip (slot : S2W_ExtractionBoundary.Slot) :
 NND_Carrier.unreply NND_Carrier.unslot (NND_Carrier.reply NND_Carrier.slot slot) = slot := by
 cases slot <;> simp only [NND_Carrier.unreply,NND_Carrier.reply,
  NND_Carrier.slot_back,NND_Carrier.error_back]

theorem M1a {W Tx : Type} : NFB_NMFBHost.M1a (W := W) (Tx := Tx) := by
 intro c
 exact roundtrip c.j.slot

theorem M1c {W Tx : Type} (c : Ctx W Tx) :
 NFB_NMFBHost.M1c c (NFB_NMFBHost.env2 c) :=
 NNH_HostEnv.environment_rep _ _ _ _

/-- The chosen reply is explicit data; no slot equation is assumed. -/
theorem reply {W Tx : Type} (c : Ctx W Tx) :
 (NFB_NMFBHost.env2 c).clock = NND_Carrier.reply NND_Carrier.slot c.j.slot := rfl
#print axioms roundtrip
#print axioms M1a
#print axioms M1c
#print axioms reply
end AspisR1.NNR_Clock
end
