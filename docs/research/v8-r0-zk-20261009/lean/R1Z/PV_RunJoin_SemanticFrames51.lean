import R1Z.PV_RunJoin_SemanticRequests51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticFrames51
open Aeneas Aeneas.Std R1Z.TranscriptR1
open PV_RunJoin_OpeningSampler50 (block)

def row (i : Fin 27) : U8 := UScalar.ofNatCore i.val (by change i.val<256;omega)

theorem row_byte (i : Fin 27) : ProverCommitOwnerBytes42.byte (row i)=i.val.toUInt8 := by
  rw [PV_RunJoin_TranscriptByteWords51.byte_salt]
  rfl

theorem absorb (r : Rec) (i : Fin 27) (framed : Slice U8)
    (hp : framed.val.map ProverCommitOwnerBytes42.byte=r.rest.framed i) :
    ProverRwOuterFrames.flatten (PV_RunJoin_SemanticRequests51.request
      (block (fieldVal (fc (.absS i)) r)) (row i) framed)=addr (.absS i) r := by
  rw [PV_RunJoin_SemanticRequests51.frame,PV_RunJoin_OpeningByteCodec51.bytes,row_byte,hp]
  rfl

theorem squeeze (r : Rec) (i : Fin 27) :
    ProverRwOuterFrames.flatten (PV_RunJoin_TranscriptRequests51.message (block (r.tr (.absS i))) 1#u8)=
      addr (.sqS i) r := by
  rw [PV_RunJoin_TranscriptFrames51.message,PV_RunJoin_OpeningByteCodec51.bytes]
  rfl

theorem advance (r : Rec) (i : Fin 27) :
    ProverRwOuterFrames.flatten (PV_RunJoin_TranscriptRequests51.message (block (r.tr (.absS i))) 2#u8)=
      addr (.advS i) r := by
  rw [PV_RunJoin_TranscriptFrames51.message,PV_RunJoin_OpeningByteCodec51.bytes]
  rfl
#print axioms row
#print axioms row_byte
#print axioms absorb
#print axioms squeeze
#print axioms advance
end R1Z.PV_RunJoin_SemanticFrames51
