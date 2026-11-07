import NNG_DomRecord26_136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomCircle0_136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136

theorem circle0 {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (alpha : Alpha) (claims : Claims) (extra : K29) (state : Array U8 32#usize)
    (t1 : r1_wire.SemanticTranscript Unit) (rec : r1_wire.ValidatedRecord) (frame : rec.framed.val.length≤3717) :
    All Checked (NNG_TreeSuffixes.f_r6 c s alpha t1 claims extra state rec) := by
  unfold NNG_TreeSuffixes.f_r6
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "circle0" (t1,rec) (c.c13 s.digest t1 rec)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.circle0 _ _ frame)
  · intro pair returned
    rcases pair with ⟨reply,t2⟩
    cases reply with
    | Ok z0 =>
      change All Checked (NNG_TreeSuffixes.f_r7 c s alpha claims extra state t2 z0)
      exact NNG_DomRecord26_136.record26 c env source s p prefixEq alpha claims extra state z0 t2
    | Err e => intro event member;cases member
#print axioms circle0
end AspisR1.NNG_DomCircle0_136
