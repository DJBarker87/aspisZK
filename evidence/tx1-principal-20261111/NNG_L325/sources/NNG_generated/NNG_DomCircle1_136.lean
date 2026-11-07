import NNG_DomPayload136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomCircle1_136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136

theorem circle1 {W : Type} (c : Calls) (s : Parent Unit W) (alpha : Alpha) (claims : Claims) (extra before : K29)
    (state : Array U8 32#usize) (z0 : aspis_core.circle.SecureCirclePoint) (t2 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717) :
    All Checked (NNG_TreeSuffixes.f_r9 c s alpha claims extra state t2 z0 before rec) := by
  unfold NNG_TreeSuffixes.f_r9
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "circle1" (t2,rec) (c.c13 s.digest t2 rec)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.circle1 _ _ frame)
  · intro pair returned
    rcases pair with ⟨reply,t3⟩
    cases reply with
    | Ok z1 =>
      change All Checked (NNG_TreeSuffixes.f_mark5 c s alpha claims extra state z0 before t3 z1)
      exact NNG_DomPayload136.mark5 c s alpha claims extra before state z0 z1 t3
    | Err e => intro event member;cases member
#print axioms circle1

theorem beforeZ1 {W : Type} (c : Calls) (s : Parent Unit W) (alpha : Alpha) (claims : Claims) (extra : K29)
    (state : Array U8 32#usize) (z0 : aspis_core.circle.SecureCirclePoint) (t2 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717) (domain : LIB_VDecode.Domain (toT14 rec) 0) :
    All Checked (NNG_TreeSuffixes.f_r8 c s alpha claims extra state t2 z0 rec (.Ok rec)) := by
  unfold NNG_TreeSuffixes.f_r8
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.beforeZ1 _ _ domain)
  · intro reply returned
    cases reply with
    | Ok before =>
      change All Checked (NNG_TreeSuffixes.f_r9 c s alpha claims extra state t2 z0 before rec)
      exact circle1 c s alpha claims extra before state z0 t2 rec frame
    | Err e => intro event member;cases member
#print axioms beforeZ1
end AspisR1.NNG_DomCircle1_136
