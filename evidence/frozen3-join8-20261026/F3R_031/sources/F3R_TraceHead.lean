import F3R_TraceSplit
set_option autoImplicit false
namespace AspisR1.F3R_TraceHead
open AspisR1PublicPreparation
open Aeneas Aeneas.Std

theorem head {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} (c : SourceFull25.Call D pre)
    (cs : List (SourceFull25.Call D pre))
    (trace : SourceFull25.Trace D pre before after (c::cs)) :
    before=c.before ∧ SourceFull25.Trace D pre c.after after cs := by
  cases trace
  exact ⟨rfl,by assumption⟩

#print axioms head
end AspisR1.F3R_TraceHead
