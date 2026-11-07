import NNG_DomArithmetic136
import NNG_DecodeReturned136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomExtra136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrayDomain

theorem extra {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal mask : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717) (domain : LIB_VDecode.Domain (toT14 rec) 87)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (maskDom : Domain mask) :
    All Checked (NNG_TreeSuffixes.f_r5 c s running terminal mask alpha t1 claims rec (.Ok rec)) := by
  unfold NNG_TreeSuffixes.f_r5
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.extra _ _ domain)
  · intro reply returned
    rw [NMT_CallTree.run_result,NMT_CallTree.erase_invoke] at returned
    rw [source.decode] at returned
    cases reply with
    | Ok extra =>
      have extraDom := NNG_DecodeReturned136.canonical 29#usize rec 87#usize extra returned
      change All Checked (NNG_TreeSuffixes.f_q1 c s running terminal mask alpha t1 claims extra (.Ok rec))
      exact NNG_DomArithmetic136.multiply fallback c env source s p prefixEq running terminal mask alpha claims extra t1 rec frame etaDom terminalDom maskDom extraDom
    | Err e => intro event member;cases member
#print axioms extra
end AspisR1.NNG_DomExtra136
