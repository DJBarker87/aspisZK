import MultiproofConeSemanticModel
import MultiproofConeRowStep
import MultiproofConeRowScalars
import MultiproofConeFrameBuild

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeSemanticRows
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft MultiproofConeCanonical MultiproofConeSlices
open MultiproofConeParserControl MultiproofConeFrameModel MultiproofConeLogicalPayload
open MultiproofConeFrameBuild
attribute [local instance] Classical.propDecidable

/-- Complete extracted owned row recurrence, including every ordinary rejection.
The proof is by row count; no 27-record wire is reduced. -/
theorem rows_total (fuel : Nat) (row : U8) (bytes : Slice U8)
    (rows : alloc.vec.Vec (alloc.vec.Vec U8))
    (height : row.val+fuel=27) (rowCount : rows.val.length=row.val)
    (wireBound : bytes.val.length≤6983) :
    (do let result ← MultiproofParserRef.parser_reference.semantic_rows row bytes rows
        ok (result.map decodedRows)) =
      ok ((semanticRows fuel row.val (bytesOf bytes.val)).map (fun tail => decodedRows rows++tail)) := by
  induction fuel generalizing row bytes rows with
  | zero =>
    have done : row>=27#u8 := by change 27≤row.val;omega
    rw [MultiproofParserRef.parser_reference.semantic_rows]
    simp only [done,if_true,core.slice.Slice.is_empty,Slice.length,bind_tc_ok,semanticRows]
    by_cases empty : bytes.val.length=0
    · have nilBytes : bytesOf bytes.val=[] := List.eq_nil_of_length_eq_zero (by
        simpa only [bytesOf,List.length_map] using empty)
      simp only [empty,decide_true,if_true,nilBytes,Option.map_some,List.append_nil]
      rfl
    · have nonempty : bytesOf bytes.val≠[] := by
        intro h
        have len := congrArg List.length h
        simp only [bytesOf,List.length_map,List.length_nil] at len
        exact empty len
      simp only [empty,decide_false,Bool.false_eq_true,if_false,nonempty,Option.map_none,bind_tc_ok]
  | succ fuel ih =>
    have rowBound : row.val<27 := by omega
    obtain ⟨tag,size,stored,finish,next,table,storage,finishEq,nextEq,tagValue,sizeValue,
      storedValue,finishValue,nextValue⟩ := MultiproofConeRowScalars.scalars_total row rowBound
    have notDone : ¬row>=27#u8 := by change ¬27≤row.val;omega
    rw [MultiproofConeRowStep.row_step row bytes rows tag size stored finish notDone table storage finishEq,
      MultiproofConeSemanticModel.row_step]
    dsimp only
    have shortIff : (bytesOf bytes.val).length<5+storedSize row.val ↔ bytes.val.length<finish.val := by
      simp only [bytesOf,List.length_map]
      omega
    by_cases short : bytes.val.length<finish.val
    · have machineShort : Slice.len bytes<finish := short
      simp only [machineShort,shortIff,short,if_true,bind_tc_ok,Option.map_none]
    · have machineShort : ¬Slice.len bytes<finish := short
      have finishBound : finish.val≤bytes.val.length := by omega
      have fiveBound : 5≤bytes.val.length := by omega
      simp only [machineShort,shortIff,short,if_false]
      rw [header_model_total row.val bytes tag size tagValue sizeValue fiveBound]
      simp only [bind_tc_ok,decide_eq_true_eq]
      by_cases header : (bytesOf bytes.val).take 5=headerBytes row.val
      · simp only [header,if_true,ne_eq,not_true_eq_false,if_false]
        have order : (5#usize).val≤finish.val := by change 5≤finish.val;omega
        rw [range_total bytes 5#usize finish order finishBound]
        simp only [bind_tc_ok]
        let payload := sub bytes 5#usize finish
        have payloadLength : payload.val.length=storedSize row.val := by
          rw [sub_length bytes 5#usize finish order finishBound]
          change finish.val-5=storedSize row.val
          omega
        have payloadBytes : bytesOf payload.val=slice (bytesOf bytes.val) 5 (storedSize row.val) := by
          simp only [payload,bytes_sub,show (5#usize).val=5 from rfl]
          rw [show finish.val-5=storedSize row.val by omega]
        simp only [←payloadBytes]
        rw [show sub bytes 5#usize finish=payload from rfl]
        by_cases good : 14≤row.val → canonical (bytesOf payload.val)
        · obtain ⟨logical,hlogical,logicalMeaning,logicalBound⟩ := good_total row payload payloadLength good
          have notBad : ¬(14≤row.val ∧ ¬canonical (bytesOf payload.val)) := fun h => h.2 (good h.1)
          simp only [hlogical,bind_tc_ok,notBad,if_false]
          obtain ⟨nextRows,hframe,frameMeaning,frameLength⟩ := framing_total bytes logical rows fiveBound
            logicalBound (by omega)
          have cont := congrArg (fun result : Result (alloc.vec.Vec (alloc.vec.Vec U8)) => do
            let nextRows ← result
            let nextRow ← row+1#u8
            let rest ← core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeFromUsizeSlice U8) bytes {start:=finish}
            MultiproofParserRef.parser_reference.semantic_rows nextRow rest nextRows) hframe
          simp only [frameAndPush,bind_assoc_eq,bind_tc_ok,nextEq,
            drop_total bytes finish finishBound] at cont
          simp only [nextEq,drop_total bytes finish finishBound,bind_tc_ok]
          rw [cont]
          have restBound : (Slice.drop bytes finish).val.length≤6983 := by
            simp only [Slice.getElem!_val_drop,List.length_drop]
            omega
          have tail := ih next (Slice.drop bytes finish) nextRows (by omega) (by omega) restBound
          rw [tail]
          have restBytes : bytesOf (Slice.drop bytes finish).val=
              (bytesOf bytes.val).drop (5+storedSize row.val) := by
            simp only [Slice.getElem!_val_drop,bytesOf,List.map_drop]
            rw [finishValue,storedValue]
          rw [restBytes,nextValue]
          cases ht : semanticRows fuel (row.val+1) ((bytesOf bytes.val).drop (5+storedSize row.val)) with
          | none => rfl
          | some suffix =>
            simp only [Option.map_some]
            rw [frameMeaning,logicalMeaning,header]
            simp only [List.append_assoc,List.singleton_append]
        · have compact : 14≤row.val := by
            by_contra h
            exact good (fun hr => False.elim (h hr))
          have bad : ¬canonical (bytesOf payload.val) := fun h => good (fun _ => h)
          rw [bad_rejected row payload payloadLength compact bad]
          simp only [compact,bad,not_false_eq_true,and_self,if_true,bind_tc_ok,Option.map_none]
      · simp only [header,if_false,ne_eq,not_false_eq_true,if_true,bind_tc_ok,Option.map_none]

#print axioms rows_total
end AspisR1.MultiproofConeSemanticRows
end
