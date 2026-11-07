import NNG_DomAddExtra136
import NNG_LIBField
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomArithmetic136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrayDomain

theorem addMask {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running mask product : Q) (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717)
    (maskDom : Domain mask) (productDom : Domain product) (extraDom : DomainArray extra) :
    All Checked (NNG_TreeSuffixes.f_q2 c s running mask product alpha t1 claims extra (.Ok rec)) := by
  unfold NNG_TreeSuffixes.f_q2
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "addMask" (mask,product) (c.c4 mask product)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.addMask _ _ ⟨maskDom,productDom⟩)
  · intro partialValue returned
    rw [NMT_CallTree.run_result,NMT_CallTree.erase_invoke] at returned
    rw [source.add] at returned
    have partialDom := NNG_LIBField.add_returned fallback mask product partialValue maskDom productDom returned
    exact NNG_DomAddExtra136.index28 c env source s p prefixEq running partialValue alpha claims extra t1 rec frame partialDom extraDom
#print axioms addMask

theorem multiply {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal mask : Q) (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (maskDom : Domain mask) (extraDom : DomainArray extra) :
    All Checked (NNG_TreeSuffixes.f_q1 c s running terminal mask alpha t1 claims extra (.Ok rec)) := by
  unfold NNG_TreeSuffixes.f_q1
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "multiply" (s.challenges.eta,terminal) (c.c5 s.challenges.eta terminal)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.multiply _ _ ⟨etaDom,terminalDom⟩)
  · intro product returned
    rw [NMT_CallTree.run_result,NMT_CallTree.erase_invoke] at returned
    rw [source.mul] at returned
    have productDom := NNG_LIBField.mul_returned fallback s.challenges.eta terminal product etaDom terminalDom returned
    exact addMask fallback c env source s p prefixEq running mask product alpha claims extra t1 rec frame maskDom productDom extraDom
#print axioms multiply
end AspisR1.NNG_DomArithmetic136
