import NNH_Run6Host
import NNW_Setup
import NNW_Claims
import NNW_Copy
import NNW_Events
import NNW_Protection
import NNW_Trace
import NNW_Recorder
import NNW_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNW_Rest
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Run5bCtx NNH_Run5bHost
variable {W Tx : Type}
 (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

/-- Exact field, with adversarial context and both native functions universal. -/
abbrev Delivered := ∀ (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second),
 (S_host L0 copy std).Extraction c n1 n2 →
 (S_host L0 copy std).Accepted1 c n1 →
 (S_host L0 copy std).Game c n1 n2 →
 (S_host L0 copy std).Queries c n1 → NNH_Run5bSplit.rest L0 copy c n1 n2

example : Delivered (Tx := Tx) L0 copy std =
 AspisR1.NNH_Run6Host.RestLaw (Tx := Tx) L0 copy std := rfl

theorem assemble : Delivered (Tx := Tx) L0 copy std := by
 intro c n1 n2 ext ac1 game queries
 have setup := NNW_Setup.produce L0 copy std c n1 n2 ext ac1 game queries
 exact ⟨setup.1,setup.2.1,setup.2.2,
  NNW_Claims.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNW_Copy.produce L0 copy std c n1 n2 ext ac1,
  NNW_Events.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNW_Protection.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNW_Trace.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNW_Recorder.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNW_Installation.produce L0 copy std c n1 n2 ext ac1 game queries⟩

#print axioms assemble
#check @assemble
end AspisR1.NNW_Rest
end
