import ExtractedSourceDigestAddresses

/-! Exact input/output pairs of reached source digest calls. Kept independent
of commitment-cut recovery so source/literal coupling need not load that proof
closure merely to describe the actual calls. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.SourceDigestLog
open Aeneas Aeneas.Std Result AspisR1
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
/-- Three actual digest input/output pairs retained by a source call. -/
def callLog {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) : List (Bytes × State) :=
  [(flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed), decodeState c.absorbed),
   (flatten (TranscriptStep.readParts c.absorbed 1#u8), decodeState c.block),
   (flatten (TranscriptStep.readParts c.absorbed 2#u8), decodeState c.state)]

def sourceLog {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) : List (Bytes × State) := cs.flatMap callLog

theorem callLog_actual {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (q : Bytes × State) (hq : q ∈ callLog c) :
    ∃ input : Slice (Slice U8), ∃ output : TranscriptStep.Bytes32,
      q = (flatten input,decodeState output) ∧ D.digest c.before.hash input = .ok output := by
  simp only [callLog,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨_,_,rfl,c.absorb⟩
  · exact ⟨_,_,rfl,c.read1⟩
  · exact ⟨_,_,rfl,c.read2⟩

theorem sourceLog_length {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) : (sourceLog cs).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [sourceLog,callLog,List.flatMap_cons] at ih ⊢; omega

theorem sourceLog_absorb_mem {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (c : SourceFull25.Call D pre) (hc : c ∈ cs) :
    (flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed),
      decodeState c.absorbed) ∈ sourceLog cs := by
  exact List.mem_flatMap.mpr ⟨c,hc,by simp [callLog]⟩


#print axioms callLog_actual
#print axioms sourceLog_length
#print axioms sourceLog_absorb_mem
end AspisR1PublicPreparation.SourceDigestLog
end
