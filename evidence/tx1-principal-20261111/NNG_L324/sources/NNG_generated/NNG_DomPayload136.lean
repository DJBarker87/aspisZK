import NNG_DomRoot136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomPayload136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_TraceAll136 NNG_TypedDomains136 NNG_AllPlain136

theorem payload {W : Type} (c : Calls) (s : Parent Unit W) (alpha : Alpha) (claims : Claims) (extra before : K29)
    (state : Array U8 32#usize) (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript Unit) :
    All Checked (NNG_TreeSuffixes.f_r10 c s alpha claims extra state z0 before t3 z1) := by
  unfold NNG_TreeSuffixes.f_r10
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "payload2" (s.prefixValue,2#u8) (c.c12 s.prefixValue 2#u8)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.payload2 _ _)
  · intro reply returned
    cases reply with
    | Ok bytes =>
      change All Checked (NNG_TreeSuffixes.f_r11 c s alpha claims extra state z0 before t3 z1 bytes)
      exact NNG_DomRoot136.copy c s alpha claims extra before state z0 z1 t3 bytes
    | Err e =>
      intro event member
      cases member
#print axioms payload

theorem guard {W : Type} (c : Calls) (s : Parent Unit W) (alpha : Alpha) (claims : Claims) (extra before : K29)
    (state : Array U8 32#usize) (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript Unit) (b : Bool) :
    All Checked (NNG_TreeSuffixes.f_circleGuard c s alpha claims extra state z0 before t3 z1 b) := by
  cases b with
  | false => exact payload c s alpha claims extra before state z0 z1 t3
  | true => intro event member;cases member
#print axioms guard

theorem compare {W : Type} (c : Calls) (s : Parent Unit W) (alpha : Alpha) (claims : Claims) (extra before : K29)
    (state : Array U8 32#usize) (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript Unit) :
    All Checked (NNG_TreeSuffixes.f_b1 c s alpha claims extra state z0 before t3 z1) := by
  unfold NNG_TreeSuffixes.f_b1
  apply NNG_AllPlain136.plain Checked
  intro b
  exact guard c s alpha claims extra before state z0 z1 t3 b
#print axioms compare

theorem mark5 {W : Type} (c : Calls) (s : Parent Unit W) (alpha : Alpha) (claims : Claims) (extra before : K29)
    (state : Array U8 32#usize) (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript Unit) :
    All Checked (NNG_TreeSuffixes.f_mark5 c s alpha claims extra state z0 before t3 z1) := by
  unfold NNG_TreeSuffixes.f_mark5
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "mark5" (s.observer,5#u8) (c.c9 s.observer 5#u8)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.mark5 _ _)
  · intro u returned
    cases u
    exact compare c s alpha claims extra before state z0 z1 t3
#print axioms mark5
end AspisR1.NNG_DomPayload136
