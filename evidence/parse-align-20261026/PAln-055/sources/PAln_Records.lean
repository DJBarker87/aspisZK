import PAln_CircleDecode
import PAln_AlignedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_Records
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

theorem zero (p : Parsed)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic) :
    rowBytes p 0=PublicInitFrame.emptyRecord := by
  have length := PSem_Rows.semanticRows_length _ _ _ _ rows
  let frame := p.semantic[0]'(by omega)
  have slot : p.semantic[0]?=some frame := List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩
  obtain ⟨payload,len,canon,same⟩ := PAln_SemanticLayout.at_index 0 p.semantic
    (PAln_SemanticLayout.layout _ _ _ _ rows) 0 frame slot
  have lengthZero : payload.length=0 := len
  have empty := List.eq_nil_of_length_eq_zero lengthZero
  have frameEq : frame=PublicInitFrame.emptyRecord := by
    rw [same,empty]
    rfl
  simpa only [rowBytes,if_pos (by decide : (0:Nat)<27),slot,Option.getD_some] using frameEq

theorem records_take (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (aligned : Aligned p tr)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic) :
    LiteralSemanticCodecBridge.records ((typedRows p q tr).take 25)=p.semantic.take 25 := by
  have length := PSem_Rows.semanticRows_length _ _ _ _ rows
  have zeroBytes := zero p rows
  apply List.ext_getElem?
  intro i
  by_cases below : i<25
  · have within : i<p.semantic.length := by omega
    let frame := p.semantic[i]'within
    have slot : p.semantic[i]?=some frame := List.getElem?_eq_some_iff.mpr ⟨within,rfl⟩
    have rowEq : rowBytes p i=frame := by simp only [rowBytes,if_pos (by omega : i<27),slot,Option.getD_some]
    by_cases first : i=0
    · subst i
      obtain ⟨root,c,initial,_⟩ := aligned.2.2.2.1
      have frameEq : frame=PublicInitFrame.emptyRecord := rowEq.symm.trans zeroBytes
      simp only [LiteralSemanticCodecBridge.records,List.getElem?_map,List.getElem?_take,if_pos below,
        typedRows,List.getElem?_mapIdx,initial,Option.map_some,restore,LiteralSemanticCodecBridge.record,slot,frameEq]
    · obtain ⟨b,c,entry,same⟩ := aligned.2.2.2.2 i (by omega) (by omega)
      simp only [LiteralSemanticCodecBridge.records,List.getElem?_map,List.getElem?_take,if_pos below,
        typedRows,List.getElem?_mapIdx,entry,Option.map_some,PAln_TypedRows.record_restore,slot]
      exact congrArg some (same.trans rowEq)
  · simp only [LiteralSemanticCodecBridge.records,List.getElem?_map,List.getElem?_take,if_neg below,Option.map_none]

#print axioms zero
#print axioms records_take
end AspisR1.PAln_Records
end
