import RPv_FJa_ClaimsOnRun
import RPv_FIr_AcceptedTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ExtraCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Canonicality of every actual extra output follows from its installed
source decoder, including the lane28 consumed by the masked endpoint. -/
theorem value (record : r1_wire.ValidatedRecord) (out : Array aspis_core.field.QM31 29#usize)
    (run : AspisS1ExtractedRoundChildren.decodeMain 29#usize record 87#usize=ok (.Ok out)) :
    ∀ x∈out.val,FIp_SemanticValues.Canon x :=
  RawActualDecodeKMainAdapter.decodeMain_success_members_canonical 29#usize record 87#usize out run
#print axioms value
end AspisR1.FJq_ExtraCanonical
end
