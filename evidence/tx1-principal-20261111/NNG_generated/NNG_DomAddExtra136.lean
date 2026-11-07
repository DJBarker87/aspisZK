import NNG_DomState136
import NNG_LIBArrayDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomAddExtra136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrayDomain

theorem addExtra {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running partialValue last : Q) (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717)
    (partialDom : Domain partialValue) (lastDom : Domain last) :
    All Checked (NNG_TreeSuffixes.f_masked_terminal c s running partialValue last alpha t1 claims extra (.Ok rec)) := by
  unfold NNG_TreeSuffixes.f_masked_terminal
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "addExtra" (partialValue,last) (c.c4 partialValue last)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.addExtra _ _ ⟨partialDom,lastDom⟩)
  · intro masked returned
    exact NNG_DomState136.compare c env source s p prefixEq running masked alpha claims extra t1 rec frame
#print axioms addExtra

theorem index28 {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running partialValue : Q) (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717)
    (partialDom : Domain partialValue) (extraDom : DomainArray extra) :
    All Checked (NNG_TreeSuffixes.f_q3 c s running partialValue alpha t1 claims extra (.Ok rec)) := by
  have selected := NNG_Array136.index extra 28#usize (by decide)
  unfold NNG_TreeSuffixes.f_q3
  rw [selected]
  exact addExtra c env source s p prefixEq running partialValue (NNG_Array136.get extra 28#usize (by decide))
    alpha claims extra t1 rec frame partialDom (get_domain extra extraDom 28#usize (by decide))
#print axioms index28
end AspisR1.NNG_DomAddExtra136
