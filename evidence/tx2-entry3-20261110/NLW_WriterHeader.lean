import NLW_ReaderHeader
set_option autoImplicit false
noncomputable section
namespace NLW_WriterHeader
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointAbiC5
/-- Symbolic structural blocks: the proof/public digest fields begin at16/48.
 No reduction of the complete checkpoint body is required. -/
theorem fields (H : Bytes → State) (proof pub : Bytes) (p : Prepared)
 (a : QueryAccumulator.State K E) :
 slice (encode H proof pub p a) 16 32=bytes (H proof) ∧
 slice (encode H proof pub p a) 48 32=bytes (H pub) := by
 let header:=OraclePortPhysicalFrameDraft.magic++[2,10,1,0,0,0,0,0]
 let rest:=
  [bytes p.state,bytes (p.roots 0),bytes (p.roots 1),encodeE p.gamma,encodeE p.kappa,
   encodeE (p.alpha 0),encodeE (p.alpha 1),encodeK p.rho,queryBytes p.queries,
   encodeKs p.semanticAlpha,encodeKs p.coordinates,encodeE p.claim,encodeE a.rhs,
   encodeK a.power,encodeKs a.weights].flatten++
  bytes (H (OraclePortPhysicalFrameDraft.domain++body p a (H proof) (H pub)))
 have layout : encode H proof pub p a=header++bytes (H proof)++(bytes (H pub)++rest) := by
  simp only [header,rest,encode,body,blocks,List.flatten_cons,List.flatten_nil,
   List.append_assoc,List.append_nil]
 have hl : header.length=16 := by simp [header,OraclePortPhysicalFrameDraft.magic]
 have bl (s : State) : (bytes s).length=32 := by simp [bytes]
 constructor
 · rw [layout]
   simpa only [hl,bl] using slice_block header (bytes (H proof)) (bytes (H pub)++rest)
 · have layout2 : encode H proof pub p a=(header++bytes (H proof))++bytes (H pub)++rest := by
    rw [layout]; simp only [List.append_assoc]
   rw [layout2]
   simpa only [List.length_append,hl,bl] using slice_block (header++bytes (H proof)) (bytes (H pub)) rest

theorem decoded (H : Bytes → State) (proof pub : Bytes) (p : Prepared)
 (a : QueryAccumulator.State K E) :
 NLW_ReaderHeader.decode (encode H proof pub p a)=some (H proof,H pub) := by
 obtain ⟨hp,hu⟩:=fields H proof pub p a
 simp only [NLW_ReaderHeader.decode,hp,hu,SemanticRecordCodec.decodeState_bytes,Option.bind_some]
#print fields
#print decoded
#print axioms fields
#print axioms decoded
end NLW_WriterHeader
