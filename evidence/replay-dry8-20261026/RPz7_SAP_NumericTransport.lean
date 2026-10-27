import RPz7_SAP_NumericFields
import F3L_PreparedExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_NumericTransport
open AspisR1CurrentCaller.InstalledPreparation

theorem numeric (out : AspisR1PublicPreparation.verifier.Prepared) :
    SAP_CurrentNumeric.numeric (currentPrepared out)=F3L_SourcePrepared.numeric out := by
  apply F3L_PreparedExt.fields
  · rfl
  · rfl
  · rfl
  · rfl
  · funext j
    change CheckpointBytes5Output.ofE (Tx1Q_Carriers.e
      (SAP_CurrentNumeric.alpha (currentPrepared out) j))=_
    rw [SAP_NumericFields.alpha]
    rfl
  · rfl
  · rfl
  · funext j
    change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k
      (SAP_CurrentNumeric.semanticAlpha (currentPrepared out) j))=_
    rw [SAP_NumericFields.semanticAlpha]
    rfl
  · funext j
    change CheckpointBytes5Output.ofK (Tx1Q_Carriers.k
      (SAP_CurrentNumeric.coordinate (currentPrepared out) j))=_
    rw [SAP_NumericFields.coordinate]
    rfl
  · rfl

#print axioms numeric
end AspisR1.SAP_NumericTransport
end
