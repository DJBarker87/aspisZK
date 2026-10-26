import F3R_SemanticChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_TraceSplit
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem split {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (trace : SourceFull25.Trace D pre before after cs) (n : Nat) :
    ∃ mid,SourceFull25.Trace D pre before mid (cs.take n) ∧
      SourceFull25.Trace D pre mid after (cs.drop n) := by
  induction n generalizing before cs with
  | zero => exact ⟨before,.nil before,trace⟩
  | succ n ih =>
    cases trace with
    | nil self=>exact ⟨self,.nil self,.nil self⟩
    | @cons after cs c tail=>
      obtain ⟨mid,left,right⟩ := ih tail
      exact ⟨mid,.cons c left,right⟩

#print axioms split
end AspisR1.F3R_TraceSplit
end
