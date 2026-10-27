import FIr_PhysicalInitial
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_PhysicalPrefix
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open MultiproofConeCanonical OraclePortCompactDraft
/-- SAME source expansion, source parser and physical parser identify all27
framed records. Used by both claim and extra literal transports. -/
theorem value (proof stored initial expanded : Slice U8) (pre : r1_wire.Prefix)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=16#usize,«end»:=7031#usize}=ok stored)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      stored initial=ok (.Ok (),expanded))
    (sourceParsed : PrefixAdapter.parseAccepted expanded=ok (.Ok pre))
    (p : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (parsed : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr=some p) :
    p.semantic=pre.records.val.map (fun s=>bytesOf s.val) ∧ OraclePortCompactDraft.Aligned p tr := by
  have sourceRows:=PSem_SemanticRows.source_rows stored initial expanded pre expand sourceParsed
  have physical:=PSem_Slices.range_bytes proof stored 16#usize 7031#usize read
  change stored.val=(proof.val.drop 16).take 7015 at physical
  have wire : bytesOf (stored.val.drop 32)=slice (bytesOf proof.val) 48 6983 := by
    rw [physical,List.drop_take,List.drop_drop]
    simp only [bytesOf,List.map_take,List.map_drop,slice]
  rw [wire] at sourceRows
  exact ⟨(FIr_PhysicalInitial.parsed_rows _ p tr parsed _ sourceRows).2,
    (OraclePortStoredParserC4.parsed _ _ _ parsed).2.2⟩
#print axioms value
end AspisR1.FJq_PhysicalPrefix
end
