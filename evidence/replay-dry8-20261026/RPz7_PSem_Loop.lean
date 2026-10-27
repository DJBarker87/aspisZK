import RPz7_PSem_RowControl
import RPz7_PSem_Iterator
set_option autoImplicit false
noncomputable section
namespace AspisR1.PSem_Loop
open Aeneas Aeneas.Std Result PSem_Control PSem_Iterator
open AspisS1NativeCompact AspisS1NativeCompactBodyFrame
open AspisS1ValuesOwnedInstallation MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames

/-- Structural composition of the actual source loop, over remaining rows.
The returned row list is derived from that loop, not supplied as a premise. -/
theorem loop_rows (fuel : Nat) (row : U8) (count : row.val+fuel=27)
    (input out updated : Slice U8) (src dst : Usize)
    (call : compact.expand_semantic_loop nativeValues (iter row) input out src dst=
      ok (.Ok (),updated)) :
    ∃ rs : List Bytes,
      PSem_Rows.expandRows fuel row.val (bytesOf (input.val.drop src.val))=some rs ∧
      bytesOf updated.val=bytesOf (out.val.take dst.val) ++ rs.flatten := by
  induction fuel generalizing row out src dst with
  | zero =>
    have atEnd : row.val=27 := by omega
    let body : State → Result (ControlFlow State Exit) :=
      fun (it,buf,s,d) => compact.expand_semantic_loop.body nativeValues input it buf s d
    change loop body (iter row,out,src,dst)=ok (.Ok (),updated) at call
    have endBody : body (iter row,out,src,dst)=
        if src != Slice.len input then ok (.done (.Err AspisR1CurrentCaller.compact.CodecError.Length,out))
        else if dst != Slice.len out then ok (.done (.Err AspisR1CurrentCaller.compact.CodecError.Length,out))
        else ok (.done (.Ok (),out)) := by
      change compact.expand_semantic_loop.body nativeValues input (iter row) out src dst=_
      rw [compact.expand_semantic_loop.body,finished row atEnd]
      rfl
    rw [loop,endBody] at call
    by_cases hs : src=Slice.len input
    · by_cases hd : dst=Slice.len out
      · simp only [hs,hd,bne_self_eq_false,if_false,bind_tc_ok] at call
        have same : out=updated := congrArg Prod.snd (Result.ok.inj call)
        subst updated
        refine ⟨[],?_,?_⟩
        · have empty : bytesOf (input.val.drop src.val)=[] := by
            simp [hs,Slice.len,Slice.length,bytesOf]
          simp [PSem_Rows.expandRows,empty]
        · simp [hd,Slice.len,Slice.length,bytesOf]
      · simp [hs,hd] at call
    · simp [hs] at call
  | succ fuel ih =>
    have bound : row.val<27 := by omega
    obtain ⟨nextRow,nextValue⟩ := successor_exists row bound
    have advance := next_row row nextRow bound nextValue
    have shapeExists : ∃ tag size, r1_wire.row_shape row=ok (some (tag,size)) := by
      rw [PSem_Shapes.table_shape]
      cases ht : ExtractedRowShape.table row with
      | none =>
        have no := (ExtractedRowShape.row_shape_none_iff row).mp
          (by rw [ExtractedRowShape.row_shape_eq_table,ht])
        omega
      | some pair => exact ⟨pair.1,pair.2,rfl⟩
    obtain ⟨tag,size,shape⟩ := shapeExists
    let body : State → Result (ControlFlow State Exit) :=
      fun (it,buf,s,d) => compact.expand_semantic_loop.body nativeValues input it buf s d
    change loop body (iter row,out,src,dst)=ok (.Ok (),updated) at call
    obtain ⟨result,step,tail⟩ := loop_success body _ _ call
    cases result with
    | done exit =>
      cases tail
      exact False.elim (PSem_RowControl.cannot_finish input out updated (iter row) (iter nextRow)
        row tag size src dst advance shape step)
    | cont next =>
      rcases next with ⟨it,buf,s,d⟩
      obtain ⟨itEq,sourceNext,destNext,sourceBound,prefixBytes⟩ :=
        PSem_RowStep.row_bytes input out buf (iter row) (iter nextRow) it row tag size src dst s d
          advance shape step
      subst it
      have nextCount : nextRow.val+fuel=27 := by omega
      obtain ⟨rs,expanded,bytes⟩ := ih nextRow nextCount buf s d tail
      have sizeEq : size.val=(rowShape row.val).2 :=
        congrArg Prod.snd (PSem_Shapes.valid_shape row tag size bound shape)
      let remaining := bytesOf (input.val.drop src.val)
      let stored := if 14 ≤ row.val then size.val/2 else size.val
      have short : ¬remaining.length<5+stored := by
        simp only [remaining,bytesOf,List.length_map,List.length_drop,stored]
        omega
      have remainder : remaining.drop (5+stored)=bytesOf (input.val.drop s.val) := by
        simp only [remaining,bytesOf,List.map_drop,List.drop_drop,stored]
        congr 2
        omega
      rw [nextValue] at expanded
      have rowPrefix : bytesOf (buf.val.take d.val)=bytesOf (out.val.take dst.val) ++
          PSem_Rows.expandedRow row.val remaining := by
        by_cases compactRow : 14 ≤ row.val <;>
          simpa [PSem_Rows.expandedRow,remaining,←sizeEq,slice,bytesOf,List.map_take,
            List.map_drop,List.drop_drop,Nat.add_comm,List.append_assoc,compactRow] using prefixBytes
      refine ⟨PSem_Rows.expandedRow row.val remaining::rs,?_,?_⟩
      · have storedEq : (if 14 ≤ row.val then (rowShape row.val).2/2 else (rowShape row.val).2)=stored := by
          rw [←sizeEq]
        change ¬(bytesOf (input.val.drop src.val)).length<5+stored at short
        change (bytesOf (input.val.drop src.val)).drop (5+stored)=_ at remainder
        simp only [PSem_Rows.expandRows,storedEq,if_neg short,remainder,expanded,
          Option.bind_some,Option.pure_def]
        rfl
      · rw [bytes,rowPrefix]
        simp only [List.flatten_cons,List.append_assoc]

#print axioms loop_rows
end AspisR1.PSem_Loop
end
