import JHf_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_EmissionAssociation
open Aeneas Aeneas.Std Result DrvC_Installation

/-- Exact slot identity of the selected source runtime model. Native syscall
and executable association remain open; this is not D188 credit. -/
theorem slot {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (JHf_Configuration.value c err)).op53=JHb_EmitAdapter.source := by
  cases c
  rfl
#print axioms slot

theorem state (s : S2I.ReturnData.State Unit Unit) :
    JHb_Emit.source JHb_EmitAdapter.runtime s JFs_PublicValue.value=
      ok (.Ok (S2I.ReturnData.set s (S2K.ResultPayload.bytes JFs_PublicValue.value).val)) :=
  JHb_Emit.real _ JHb_EmitAdapter.runtime_law _
#print axioms state

theorem accepted {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (JHf_Configuration.value c err)).op53 JGx_RealStatement.value=ok (.Ok ()) := by
  rw [slot]
  exact JHb_EmitAdapter.accepted
#print axioms accepted
end AspisR1.JHf_EmissionAssociation
end
