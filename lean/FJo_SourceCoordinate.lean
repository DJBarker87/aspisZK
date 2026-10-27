import FJo_Tx1Scratch
import FJi_SelectedPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_SourceCoordinate
open Aeneas Aeneas.Std Result
open AspisR1ClaimPreparedBridge AspisR1CurrentCaller.InstalledPreparation
abbrev P := AspisR1PublicPreparation.aspis_core.field.WideExact
/-- Nominal field adapters preserve the SAME source coordinate and canonicality. -/
theorem canonical (x : P) (h : AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE x)) :
    FIo_WideValues.Canon (FIo_Install.toE (Tx1Q_Carriers.e (currentE x))) := by
  exact ⟨⟨h.1.1,h.1.2⟩,⟨h.2.1,h.2.2⟩⟩
theorem value (x : P) :
    AspisR1CurrentWide.Proof.decodeWide
      (FIo_FieldBridge.wide (FIo_Install.toE (Tx1Q_Carriers.e (currentE x))))=
        AspisR1CurrentPreparedClaim.Concrete.decode (toClaimE x) := by
  rfl
#print axioms canonical
#print axioms value
end AspisR1.FJo_SourceCoordinate
end
