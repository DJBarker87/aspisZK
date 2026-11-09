import NNH8_RestParts
import NNH8_RestProtection
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH8_Rest
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NOC_Run5bCtx NOC_Run5bHost
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
 (S_host L0 copy std).Queries c n1 → NNH8_Split.rest L0 copy c n1 n2

/-- The TFM.Split.rest field type at the corrected host, written out from TFM.Split. -/
example (rest : Delivered (Tx := Tx) L0 copy std) : RSL.TFM.Split (S_host (Tx := Tx) L0 copy std) :=
 ⟨NNH8_Split.rest L0 copy, NNH8_Split.outcome L0 copy, NNH8_Split.conclusion_iff L0 copy, rest⟩

theorem assemble : Delivered (Tx := Tx) L0 copy std := by
 intro c n1 n2 ext ac1 game queries
 have setup := NNH8_RestSetup.produce L0 copy std c n1 n2 ext ac1 game queries
 exact ⟨setup.1,setup.2.1,setup.2.2,
  NNH8_RestClaims.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNH8_RestCopy.produce L0 copy std c n1 n2 ext ac1,
  NNH8_RestEvents.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNH8_Protection.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNH8_RestTrace.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNH8_RestRecorder.produce L0 copy std c n1 n2 ext ac1 game queries,
  NNH8_RestInstallation.produce L0 copy std c n1 n2 ext ac1 game queries⟩

#print axioms AspisR1.NNH8_Rest.assemble
#check @assemble
end AspisR1.NNH8_Rest
end
