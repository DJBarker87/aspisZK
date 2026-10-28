import NCA_BytePort
set_option autoImplicit false
namespace AspisR1.NCA_CheckPort
open Aeneas Aeneas.Std Result OraclePortCompactDraft MultiproofConeCanonical

theorem source (input : Slice U8) (aligned : input.val.length%16=0)
    (canonical : OraclePortCompactDraft.canonical (bytesOf input.val)) :
    LPt_External.compact.check_values input=ok (.Ok ()) := by
  have chunks := (S8JoinCompactChunks.canonical_chunks (bytesOf input.val)
    (by simpa only [bytesOf,List.length_map] using aligned)).mp canonical
  have good : LPt_LPl_Kit_Bytes.chunksValid 16 4 false input.val=true := by
    unfold LPt_LPl_Kit_Bytes.chunksValid
    apply List.all_eq_true.mpr
    intro i hi
    have bound : i < input.val.length/16 := List.mem_range.mp hi
    apply NCA_BytePort.canonical_chunk
    · simp only [List.length_take,List.length_drop]
      omega
    · rw [NCA_BytePort.window]
      exact chunks i (by simpa only [bytesOf,List.length_map] using bound)
  simp only [LPt_External.compact.check_values,good,ite_true]

/-- The accepted scan's SAME stored y1 range discharges NBR's check premise.
No parsed row list or independently chosen compact buffer enters. -/
theorem y1 (proof : Slice U8) (full : proof.val.length=57607)
    (scan : OraclePortCompactDraft.scan (bytesOf proof.val)) :
    LPt_External.compact.check_values (NBR_ProducerBuffers.compactInput proof)=ok (.Ok ()) := by
  have length : (NBR_ProducerBuffers.compactInput proof).val.length=464 :=
    NBR_RangeGeometry.length proof 7031#usize 7495#usize 464 (by scalar_tac) (by change 7495≤_;omega)
  apply source _ (by omega)
  change OraclePortCompactDraft.canonical (bytesOf ((proof.val.drop 7031).take 464))
  rw [NCA_BytePort.window]
  exact scan.1

#print axioms source
#print axioms y1
end AspisR1.NCA_CheckPort
