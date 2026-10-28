import NDO_JFu_TerminalCallback
import NDO_JFv_DecodeCanonical
import RPt_FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TerminalCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

abbrev Canon (q : FIq_Native.field.QM31) := FIp_SemanticValues.Canon (FIq_Carriers.fromQ q)

theorem transport (q : MainQM) (h : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (genQToProbe (mainToGen q))) :
    Canon (FIq_Carriers.toQ q) := by
  change (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
    (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647) at h ⊢
  exact h

theorem cell0 (j : Fin 29) : Canon (FIq_Carriers.toQ (JFu_ClaimsData.a0.val[j.val]'(by rw [JFu_ClaimsData.a0.property];exact j.isLt))) :=
  transport _ (JFv_DecodeCanonical.source JFu_Q25Source.record 0#usize _ JFu_ClaimsData.decode0 j)

theorem cell1 (j : Fin 29) : Canon (FIq_Carriers.toQ (JFu_ClaimsData.a1.val[j.val]'(by rw [JFu_ClaimsData.a1.property];exact j.isLt))) :=
  transport _ (JFv_DecodeCanonical.source JFu_Q25Source.record 29#usize _ JFu_ClaimsData.decode1 j)

theorem cell2 (j : Fin 29) : Canon (FIq_Carriers.toQ (JFu_ClaimsData.a2.val[j.val]'(by rw [JFu_ClaimsData.a2.property];exact j.isLt))) :=
  transport _ (JFv_DecodeCanonical.source JFu_Q25Source.record 58#usize _ JFu_ClaimsData.decode2 j)

theorem source (r : Fin 3) (j : Fin 29) : Canon
    ((JFu_TerminalCallback.claims.val[r.val]'(by rw [JFu_TerminalCallback.claims.property];exact r.isLt)).val[j.val]'(by
      rw [(JFu_TerminalCallback.claims.val[r.val]'(by rw [JFu_TerminalCallback.claims.property];exact r.isLt)).property]
      exact j.isLt)) := by
  fin_cases r
  · simpa only [JFu_TerminalCallback.claims,FIq_Carriers.mapArray,JFu_ClaimsData.claims,
      List.getElem_map,List.getElem_cons_zero,List.getElem_cons_succ] using cell0 j
  · simpa only [JFu_TerminalCallback.claims,FIq_Carriers.mapArray,JFu_ClaimsData.claims,
      List.getElem_map,List.getElem_cons_zero,List.getElem_cons_succ] using cell1 j
  · simpa only [JFu_TerminalCallback.claims,FIq_Carriers.mapArray,JFu_ClaimsData.claims,
      List.getElem_map,List.getElem_cons_zero,List.getElem_cons_succ] using cell2 j

#print axioms transport
#print axioms cell0
#print axioms cell1
#print axioms cell2
#print axioms source
end AspisR1.JFu_TerminalCanonical
end
