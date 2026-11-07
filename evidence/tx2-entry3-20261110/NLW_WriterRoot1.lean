import NLW_WriterRoot0
set_option autoImplicit false
noncomputable section
namespace NLW_WriterRoot1
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointAbiC5
/-- Second root has its own structural position; no free Parsed root1 witness
is substituted for the original semantic commitment. -/
theorem encoded (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
 (a : QueryAccumulator.State K E) :
 slice (encode H stored pub p a) 144 32=bytes (p.roots 1) := by
 let header:=OraclePortPhysicalFrameDraft.magic++[2,10,1,0,0,0,0,0]
 let pre:=header++bytes (H stored)++bytes (H pub)++bytes p.state++bytes (p.roots 0)
 let after:=
  [encodeE p.gamma,encodeE p.kappa,encodeE (p.alpha 0),encodeE (p.alpha 1),
   encodeK p.rho,queryBytes p.queries,encodeKs p.semanticAlpha,encodeKs p.coordinates,
   encodeE p.claim,encodeE a.rhs,encodeK a.power,encodeKs a.weights].flatten++
  bytes (H (OraclePortPhysicalFrameDraft.domain++body p a (H stored) (H pub)))
 have layout : encode H stored pub p a=pre++bytes (p.roots 1)++after := by
  simp only [pre,after,header,encode,body,blocks,List.flatten_cons,List.flatten_nil,
   List.append_assoc,List.append_nil]
 have preLength : pre.length=144 := by
  simp [pre,header,bytes,OraclePortPhysicalFrameDraft.magic]
 have rootLength : (bytes (p.roots 1)).length=32 := by simp [bytes]
 rw [layout]
 simpa only [preLength,rootLength] using slice_block pre (bytes (p.roots 1)) after
#print encoded
#print axioms encoded
end NLW_WriterRoot1
