import NDI_TranscriptRef.Funs
import NDI_TranscriptInit
set_option autoImplicit false
namespace NDI_TranscriptBridge
open Aeneas Aeneas.Std Result
open NDI_TranscriptLaw

theorem initialize {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (publicBytes : Slice U8) (root reply : Bytes32)
    (cap : publicBytes.val.length≤1880)
    (digest : D.digest hash (newParts publicBytes root
      (UScalar.cast .U32 (Slice.len publicBytes)))=ok reply) :
    (do let packet ← NDI_TranscriptRef.transcript_new_ref reply
        ok (core.result.Result.Ok
          ({state:=packet.1,hash:=hash,next_row:=packet.2.1} :
            AspisR1PublicPreparation.r1_wire.SemanticTranscript H))) =
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.new D hash publicBytes root := by
  simp only [NDI_TranscriptRef.transcript_new_ref,bind_tc_ok]
  exact (NDI_TranscriptInit.reference D hash publicBytes root reply cap digest).symm

theorem sample {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (self : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (row tag next : U8) (framed : Slice U8) (absorbed block advanced : Bytes32)
    (same : self.next_row=row) (addTag : 160#u8+row=ok tag) (inc : row+1#u8=ok next)
    (absorb : D.digest self.hash (absorbParts self.state tag framed)=ok absorbed)
    (squeeze : D.digest self.hash (taggedParts absorbed 1#u8)=ok block)
    (advance : D.digest self.hash (taggedParts absorbed 2#u8)=ok advanced) :
    (do let packet ← NDI_TranscriptRef.transcript_sample_ref block advanced row
        ok (core.result.Result.Ok packet.1,
          {self with state:=packet.2.1,next_row:=packet.2.2.1})) =
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated D self row framed := by
  simp only [NDI_TranscriptRef.transcript_sample_ref,inc,bind_tc_ok]
  exact (NDI_TranscriptLaw.sample D self row tag next framed absorbed block advanced
    same addTag inc absorb squeeze advance).symm

#print axioms initialize
#print axioms sample
end NDI_TranscriptBridge
