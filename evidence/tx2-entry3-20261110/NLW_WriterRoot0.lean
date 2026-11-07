import CheckpointBytes5Writer
set_option autoImplicit false
noncomputable section
namespace NLW_WriterRoot0
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointAbiC5
/-- Structural block extraction only; never normalize a1736/1768-byte
encoded recurrence or finite universe. -/
theorem encoded (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
 (a : QueryAccumulator.State K E) :
 slice (encode H stored pub p a) 112 32=bytes (p.roots 0) := by
 let header:=OraclePortPhysicalFrameDraft.magic++[2,10,1,0,0,0,0,0]
 let pre:=header++bytes (H stored)++bytes (H pub)++bytes p.state
 let after:=
  [bytes (p.roots 1),encodeE p.gamma,encodeE p.kappa,encodeE (p.alpha 0),encodeE (p.alpha 1),
   encodeK p.rho,queryBytes p.queries,encodeKs p.semanticAlpha,encodeKs p.coordinates,
   encodeE p.claim,encodeE a.rhs,encodeK a.power,encodeKs a.weights].flatten++
  bytes (H (OraclePortPhysicalFrameDraft.domain++body p a (H stored) (H pub)))
 have layout : encode H stored pub p a=pre++bytes (p.roots 0)++after := by
  simp only [pre,after,header,encode,body,blocks,List.flatten_cons,List.flatten_nil,
   List.append_assoc,List.append_nil]
 have preLength : pre.length=112 := by
  simp [pre,header,bytes,OraclePortPhysicalFrameDraft.magic]
 have rootLength : (bytes (p.roots 0)).length=32 := by simp [bytes]
 rw [layout]
 simpa only [preLength,rootLength] using slice_block pre (bytes (p.roots 0)) after
#print encoded
#print axioms encoded
end NLW_WriterRoot0
