import F3R_TraceSplit
set_option autoImplicit false
namespace AspisR1.F3R_TraceAppend
open AspisR1PublicPreparation

theorem append {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {before mid after : r1_wire.SemanticTranscript H} {left right : List (SourceFull25.Call D pre)}
    (a : SourceFull25.Trace D pre before mid left) (b : SourceFull25.Trace D pre mid after right) :
    SourceFull25.Trace D pre before after (left++right) := by
  induction a with
  | nil => exact b
  | cons c tail ih =>exact .cons c (ih b)

#print axioms append
end AspisR1.F3R_TraceAppend
