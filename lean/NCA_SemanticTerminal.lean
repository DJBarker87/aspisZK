import NCA_FullCarrierLoop
set_option autoImplicit false
namespace AspisR1.NCA_SemanticTerminal
open Aeneas Aeneas.Std Result ControlFlow
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator

theorem restore_identity (logical : Slice U8) (full : logical.val.length=14759) :
    NCA_FullCarrierRow.restore logical (NBR_ProducerBuffers.semanticInitial logical)=logical := by
  have size : (NBR_ProducerBuffers.semanticInitial logical).val.length=13831 :=
    NBR_RangeGeometry.length logical 0#usize 13831#usize 13831 (by scalar_tac)
      (by change 13831≤_;omega)
  apply Subtype.ext
  change logical.val.setSlice! 0 (NBR_ProducerBuffers.semanticInitial logical).val=logical.val
  rw [NCA_SemanticRestore.source logical _ full size]
  change (logical.val.drop 0).take (13831-0)++logical.val.drop 13831=logical.val
  rw [List.drop_zero,Nat.sub_zero,List.take_append_drop]

/-- Exact final iterator and source/destination checks from the same complete
carrier. This supplies the terminal body after NCA_FullCarrierLoop.source. -/
theorem source (input logical : Slice U8) (row : U8) (src dst : Usize)
    (inputLength : input.val.length=7015) (full : logical.val.length=14759)
    (rowEnd : row.val=27) (sourceEnd : src.val=7015) (destEnd : dst.val=13831) :
    compact.expand_semantic_loop.body nativeValues input (iter row)
      (NBR_ProducerBuffers.semanticInitial logical) src dst=
        ok (.done (.Ok (),NBR_ProducerBuffers.semanticInitial logical)) := by
  have size : (NBR_ProducerBuffers.semanticInitial logical).val.length=13831 :=
    NBR_RangeGeometry.length logical 0#usize 13831#usize 13831 (by scalar_tac)
      (by change 13831≤_;omega)
  have hs : src=Slice.len input := UScalar.eq_of_val_eq (sourceEnd.trans inputLength.symm)
  have hd : dst=Slice.len (NBR_ProducerBuffers.semanticInitial logical) :=
    UScalar.eq_of_val_eq (destEnd.trans size.symm)
  unfold compact.expand_semantic_loop.body
  rw [finished row rowEnd]
  change (if src != Slice.len input then _ else if dst != Slice.len _ then _ else _)=_
  simp only [hs,hd,bne_self_eq_false,if_false]
  rfl

#print axioms restore_identity
#print axioms source
end AspisR1.NCA_SemanticTerminal
