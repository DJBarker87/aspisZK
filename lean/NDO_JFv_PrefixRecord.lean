import JFv_Decode
import NDO_JFv_Buffers
import RPz7_NP6_ParsedClaims
set_option autoImplicit false
namespace AspisR1.JFv_PrefixRecord
open Aeneas Aeneas.Std Result WP
open AspisR1PublicPreparation

theorem record (pre : r1_wire.Prefix) (row : U8) (bound : row.val<27) :
    ∃ frame,r1_wire.Prefix.record pre row=ok (.Ok frame) := by
  have total : r1_wire.Prefix.record pre row ⦃ result => ∃ frame,result=.Ok frame ⦄ := by
    unfold r1_wire.Prefix.record
    step*
  obtain ⟨result,call,frame,same⟩ := WP.spec_imp_exists total
  exact ⟨frame,by rw [same] at call;exact call⟩

theorem validated (pre : r1_wire.Prefix) (row : U8) (bound : row.val<27) :
    ∃ vr,r1_wire.Prefix.validated_record pre row=ok (.Ok vr) := by
  obtain ⟨frame,call⟩ := record pre row bound
  refine ⟨⟨row,frame⟩,?_⟩
  simp only [r1_wire.Prefix.validated_record,call,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]

#print axioms record
#print axioms validated
end AspisR1.JFv_PrefixRecord
