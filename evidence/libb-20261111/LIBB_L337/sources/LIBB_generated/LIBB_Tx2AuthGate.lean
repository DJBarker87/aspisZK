import LIBB_ReturnObservation
import LIBB_Tx2Auth
set_option autoImplicit false
noncomputable section
namespace LIBB_Tx2AuthGate
open LIBB_ReturnFunctional
/-- Ruling (bq) gate for the full stopped-prefix source field, including
returned events. No domain restriction is needed for this uniqueness law. -/
theorem returnFunctional (pub proof ck : RSL.Bytes) :
 ReturnFunctional (LIBB_Tx2Auth.law pub proof ck) := by
 unfold LIBB_Tx2Auth.law
 split
 · exact LIBB_ReturnObservation.functional _ _ _
 · intro env o₁ o₂ r₁ r₂ h₁ h₂ ret₁ ret₂
   change o₁=⟨.abort,[]⟩ at h₁
   subst o₁
   cases ret₁

/-- The same returned observation equals the deterministic source graph;
its events are part of this equality. -/
theorem returned_resolved (pub proof ck : RSL.Bytes) (env : RSL.Env)
 (o : RSL.Obs (Except LIBB_V2Carriers.VErr Unit)) (r : Except LIBB_V2Carriers.VErr Unit)
 (law : LIBB_Tx2Auth.law pub proof ck env o) (returned : o.exit=.ret r) :
 LIBB_Tx2Auth.resolved pub proof ck env o := by
 unfold LIBB_Tx2Auth.law at law
 unfold LIBB_Tx2Auth.resolved
 split at law
 · rename_i fits
   rw [dif_pos fits]
   exact LIBB_ReturnObservation.resolved env _ _ _ o r law returned
 · change o=⟨.abort,[]⟩ at law
   subst o
   cases returned
#print axioms returnFunctional
#print axioms returned_resolved
end LIBB_Tx2AuthGate
end
