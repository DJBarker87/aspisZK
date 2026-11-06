import NJM_RoundsPacket
set_option autoImplicit false
namespace AspisR1.NJM_TranscriptFrame
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Hash carrier is immutable even on a returning Rust error. This is the
full source field, not an inference from the two native state windows. -/
def KeepsHash {A H : Type} (hash : H)
 (reply : Result (core.result.Result A r1_wire.Error × r1_wire.SemanticTranscript H)) : Prop :=
 match reply with | .ok (_,after)=>after.hash=hash | .fail _=>True | .div=>True

theorem bind_frame {A B H : Type} (hash : H) (reply : Result A)
 (next : A→Result (core.result.Result B r1_wire.Error × r1_wire.SemanticTranscript H))
 (frame : ∀ a,KeepsHash hash (next a)) : KeepsHash hash (reply >>= next) := by
 cases reply with
 | ok a=>exact frame a
 | fail _=>trivial
 | div=>trivial

theorem block {H : Type} (D : aspis_core.Digest32 H) (before : r1_wire.SemanticTranscript H)
 (row : U8) (framed : Slice U8) :
 KeepsHash before.hash (r1_wire.SemanticTranscript.sample_block_validated D before row framed) := by
 unfold r1_wire.SemanticTranscript.sample_block_validated
 split
 · rfl
 · repeat' first
    | (apply bind_frame;intro value)
    | (solve | rfl)

theorem semantic {H : Type} (D : aspis_core.Digest32 H) (before : r1_wire.SemanticTranscript H)
 (record : r1_wire.ValidatedRecord) :
 KeepsHash before.hash (r1_wire.SemanticTranscript.semantic_validated D before record) := by
 simp only [r1_wire.SemanticTranscript.semantic_validated,r1_wire.ValidatedRecord.impl.row,
  r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
 split
 · rfl
 · have frame:=block D before record.row record.framed
   generalize call : r1_wire.SemanticTranscript.sample_block_validated D before record.row record.framed=reply at frame ⊢
   cases reply with
   | fail _=>trivial
   | div=>trivial
   | ok pair=>
     rcases pair with ⟨inner,after⟩
     cases inner with
     | Err error=>exact frame
     | Ok block=>
       change KeepsHash before.hash (do
        let q←AspisR1PublicPreparation.sampler.qm31_sample block
        ok (.Ok q,after))
       apply bind_frame
       intro q
       exact frame

/-- Exact successful round frame, internally derived from its actual
semantic call; the successful-step premise is a local invariant helper. -/
theorem round {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (before after : r1_wire.SemanticTranscript H) (a next : NIX_CertificateFrames.Alpha)
 (running value : aspis_core.field.QM31) (r : Usize) (bound : r.val<10)
 (call : (PreparedHashCode.run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre before a running r)).2=ok (.Ok (value,next,after))) :
 after.hash=before.hash := by
 have erased : RoundModel.step NJM_RoundJoin.R D pre before a running r=ok (.Ok (value,next,after)) := by
  rw [PreparedHashCode.run_value,S1SemanticCode.roundStep_erasure] at call
  exact call
 obtain ⟨record,q,getter,sampled,updated⟩:=RoundCalls.step_success NJM_RoundJoin.R D pre before after a next running value r
  (NJG_RoundProducer.row r bound) (NJG_RoundProducer.row_add r bound) erased
 have frame:=semantic D before record
 rw [sampled] at frame
 exact frame

#print axioms bind_frame
#print axioms block
#print axioms semantic
#print axioms round
end AspisR1.NJM_TranscriptFrame
