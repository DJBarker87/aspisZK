import NDO_JFw_Row
import JFw_Geometry
set_option autoImplicit false
namespace AspisR1.JFw_Loop
open Aeneas Aeneas.Std Result WP ControlFlow
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator JFw_Geometry

theorem success (fuel : Nat) (row : U8) (count : row.val+fuel = 27)
    (input out : Slice U8) (src dst : Usize)
    (inputLength : input.length = 7015) (outLength : out.length = 13831)
    (source : src.val = sourcePos row.val) (dest : dst.val = destPos row.val) :
    ∃ updated, compact.expand_semantic_loop nativeValues (iter row) input out src dst =
      ok (.Ok (),updated) := by
  induction fuel generalizing row out src dst with
  | zero =>
    have atEnd : row.val = 27 := by omega
    have hs : src = Slice.len input := by
      apply UScalar.eq_of_val_eq
      change src.val = input.length
      rw [source,atEnd,inputLength]
      rfl
    have hd : dst = Slice.len out := by
      apply UScalar.eq_of_val_eq
      change dst.val = out.length
      rw [dest,atEnd,outLength]
      rfl
    have body : compact.expand_semantic_loop.body nativeValues input (iter row) out src dst =
        ok (.done (.Ok (),out)) := by
      unfold compact.expand_semantic_loop.body
      rw [finished row atEnd]
      change (if src != Slice.len input then _ else if dst != Slice.len out then _ else _) = _
      simp only [hs,hd,bne_self_eq_false,if_false]
      rfl
    refine ⟨out,?_⟩
    unfold compact.expand_semantic_loop
    unfold loop
    dsimp only
    rw [body]

  | succ fuel ih =>
    have bound : row.val < 27 := by omega
    obtain ⟨nextRow,next⟩ := successor_exists row bound
    obtain ⟨tag,size,shape⟩ : ∃ tag size, r1_wire.row_shape row=ok (some (tag,size)) := by
      rw [PSem_Shapes.table_shape]
      cases ht : ExtractedRowShape.table row with
      | none =>
        have no := (ExtractedRowShape.row_shape_none_iff row).mp
          (by rw [ExtractedRowShape.row_shape_eq_table,ht])
        omega
      | some pair => exact ⟨pair.1,pair.2,rfl⟩
    have sizeEq : size.val = (OraclePortCompactDraft.rowShape row.val).2 :=
      congrArg Prod.snd (PSem_Shapes.valid_shape row tag size bound shape)
    obtain ⟨sb,aligned,sp,dp,ib,ob⟩ := JFw_Geometry.step row.val bound
    obtain ⟨result,call,buf,s,d,resultEq,sValue,dValue⟩ :=
      spec_imp_exists (JFw_Row.spec input out row nextRow tag size src dst bound next shape
        (by omega) (by omega) (by rw [source,sizeEq,inputLength,←sp];exact ib)
        (by rw [dest,sizeEq,outLength,←dp];exact ob) (by omega) (by omega))
    subst result
    have length : buf.length = out.length :=
      AspisS1NativeCompactLengths.body_length nativeValues input out (iter row) src dst _ call
    have nextSource : s.val = sourcePos nextRow.val := by rw [sValue,source,sizeEq,←sp,next]
    have nextDest : d.val = destPos nextRow.val := by rw [dValue,dest,sizeEq,←dp,next]
    obtain ⟨updated,tail⟩ := ih nextRow (by omega) buf s d (length.trans outLength) nextSource nextDest
    refine ⟨updated,?_⟩
    unfold compact.expand_semantic_loop at tail ⊢
    unfold loop
    dsimp only
    rw [call]
    exact tail

#print axioms success
end AspisR1.JFw_Loop
