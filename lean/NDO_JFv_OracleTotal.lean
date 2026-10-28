import NDO_JFv_PrefixCall
import RPz7_F3V_OracleDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_OracleTotal
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem retained {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) :
    JFv_TranscriptTotal.Total
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current H D)) := by
  intro hash parts
  exact ⟨_,rfl⟩

#print axioms retained
end AspisR1.JFv_OracleTotal
end
