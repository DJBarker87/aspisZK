import R1Z.PV_RunJoin_TranscriptFrames51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OriginalOpeningFrames51
open Aeneas Aeneas.Std R0Z.FsStatement R1Z.TranscriptR1
open PV_RunJoin_OpeningSampler50 (block)
open ProverRwOuterFrames (flatten)

def row (i : Fin 4) : U8 := UScalar.ofNatCore (27+i.val) (by omega)

theorem row_byte (i : Fin 4) : ProverCommitOwnerBytes42.byte (row i)=(27+i.val).toUInt8 := by
  rw [PV_RunJoin_TranscriptByteWords51.byte_salt]
  rfl

theorem absorb (r : Rec) (i : Fin 4) (payload : Slice U8) (small : payload.length≤U32.max)
    (hp : payload.val.map ProverCommitOwnerBytes42.byte=r.rest.payload i) :
    flatten (PV_RunJoin_TranscriptAbsorb51.request (block (fieldVal (fc (.absO i)) r)) (row i) payload)=
      addr (.absO i) r := by
  rw [PV_RunJoin_TranscriptFrames51.absorb _ _ _ small,
    PV_RunJoin_OpeningByteCodec51.bytes,row_byte,hp]
  have len : payload.length=(r.rest.payload i).length := by
    rw [←hp,List.length_map];rfl
  rw [len]
  rfl

theorem squeeze (r : Rec) (i : Fin 4) :
    flatten (PV_RunJoin_TranscriptRequests51.message (block (r.tr (.absO i))) 1#u8)=addr (.sqO i) r := by
  rw [PV_RunJoin_TranscriptFrames51.message,PV_RunJoin_OpeningByteCodec51.bytes]
  rfl

theorem advance (r : Rec) (i : Fin 4) :
    flatten (PV_RunJoin_TranscriptRequests51.message (block (r.tr (.absO i))) 2#u8)=addr (.advO i) r := by
  rw [PV_RunJoin_TranscriptFrames51.message,PV_RunJoin_OpeningByteCodec51.bytes]
  rfl
#print axioms row
#print axioms row_byte
#print axioms absorb
#print axioms squeeze
#print axioms advance
end R1Z.PV_RunJoin_OriginalOpeningFrames51
