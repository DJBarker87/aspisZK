import NNG_DomCircle0_136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomState136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136

theorem state {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717) :
    All Checked (NNG_TreeSuffixes.f_state_before_z0 c s alpha t1 claims extra (.Ok rec)) := by
  unfold NNG_TreeSuffixes.f_state_before_z0
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "state" t1 (c.c14 s.digest t1)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.state _ _)
  · intro bytes returned
    change All Checked (NNG_TreeSuffixes.f_r6 c s alpha t1 claims extra bytes rec)
    exact NNG_DomCircle0_136.circle0 c env source s p prefixEq alpha claims extra bytes t1 rec frame
#print axioms state

theorem mark4 {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717) :
    All Checked (NNG_TreeSuffixes.f_mark4 c s alpha t1 claims extra (.Ok rec)) := by
  unfold NNG_TreeSuffixes.f_mark4
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "mark4" (s.observer,4#u8) (c.c9 s.observer 4#u8)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.mark4 _ _)
  · intro u returned
    cases u
    exact state c env source s p prefixEq alpha claims extra t1 rec frame
#print axioms mark4

theorem guard {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717) (b : Bool) :
    All Checked (NNG_TreeSuffixes.f_terminalGuard c s alpha t1 claims extra b (.Ok rec)) := by
  cases b with
  | false => exact mark4 c env source s p prefixEq alpha claims extra t1 rec frame
  | true => intro event member;cases member
#print axioms guard

theorem compare {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running masked : Q) (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript Unit)
    (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717) :
    All Checked (NNG_TreeSuffixes.f_b c s running masked alpha t1 claims extra (.Ok rec)) := by
  unfold NNG_TreeSuffixes.f_b
  apply NNG_AllPlain136.plain Checked
  intro b
  exact guard c env source s p prefixEq alpha claims extra t1 rec frame b
#print axioms compare
end AspisR1.NNG_DomState136
