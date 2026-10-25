import Port11PROV_WriterRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_CheckpointRoots
open Aeneas Aeneas.Std Result VTop_Stages
open MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Both stored roots of the actual current18 return are the roots written
from the SAME physical Prepared into the SAME saved Vec. No BodyMatches,
canonical preparation or collision/no-hit premise is needed. -/
theorem accepted (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (p0 p1 : verifier.Prepared) (written a1 : verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (wrote : Port3_CheckpointInstall.writer D p0 written proof pub hash=ok saved)
    (resumed : Port6CK_Reader.reader reserved unwrap D saved.deref proof pub .S2 hash=ok (.Ok (p1,a1))) :
    Port3_BatchStage.root0 p1=Port3_BatchStage.root0 p0 ∧
    Port3_BatchStage.root1 p1=Port3_BatchStage.root1 p0 := by
  obtain ⟨len,r0,r1⟩ := Port11PROV_WriterRoots.saved D hash p0 written proof pub saved wrote
  have retained := Port6CK_Reader.accepted reserved unwrap unwrap_ok D hash saved.deref proof pub p1 a1 resumed
  rw [Port4A_ReaderInstall.reference_eq] at retained
  have native := Port3_CheckpointInstall.reader_success reserved D saved.deref proof pub .S2 hash p1 a1 retained
  obtain ⟨f⟩ := OraclePortCkptAbiSourceFields.successful_fields _ _ saved.deref proof pub .S2 hash p1 a1 native
  have flat := CheckpointBytes4Layout.flat_fields reserved saved.deref p1 a1 f len
  have zero : Port3_BatchStage.root0 p1=f.root0 := by
    simp only [Port3_BatchStage.root0,f.roots,Array.make,List.getElem_cons_zero]
  have one : Port3_BatchStage.root1 p1=f.root1 := by
    simp only [Port3_BatchStage.root1,f.roots,Array.make,List.getElem_cons_succ,List.getElem_cons_zero]
  constructor
  · rw [zero]
    apply Subtype.ext
    apply MultiproofConeByteEquality.bytes_injective
    have raw := congrArg bytesOf flat.root0Bytes
    simp only [bytesOf,List.map_take,List.map_drop] at raw
    exact raw.trans r0
  · rw [one]
    apply Subtype.ext
    apply MultiproofConeByteEquality.bytes_injective
    have raw := congrArg bytesOf flat.root1Bytes
    simp only [bytesOf,List.map_take,List.map_drop] at raw
    exact raw.trans r1

#print axioms accepted
end AspisR1.Port11PROV_CheckpointRoots
end
