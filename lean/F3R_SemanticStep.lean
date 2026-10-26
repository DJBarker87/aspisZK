import F3J_ValidatedLog
import F3J_SourceBlockValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_SemanticStep
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem returned {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (below : c.row.val<25) :
    erase (S1SemanticCode.semanticValidated D c.before c.record)=ok (.Ok c.q,c.after) := by
  rw [S1SemanticCode.semanticValidated_erasure]
  exact c.semantic

#print axioms returned
end AspisR1.F3R_SemanticStep
end
