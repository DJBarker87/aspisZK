import NCA_SemanticRestore
import NBR_SemanticStep
set_option autoImplicit false
namespace AspisR1.NCA_FullCarrierRow
open Aeneas Aeneas.Std Result ControlFlow
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator

def restore (logical semantic : Slice U8) : Slice U8 :=
  ⟨logical.val.setSlice! 0 semantic.val,by rw [List.length_setSlice!];exact logical.property⟩

theorem length (logical semantic : Slice U8) :
    (restore logical semantic).val.length=logical.val.length := List.length_setSlice! _ _ _

/-- One row on the original complete logical carrier. The post-carrier is
EXACTLY mutable-borrow restoration on that carrier; it is not independently
chosen to have compatible projections. Native full-frame association remains
an explicit P6 obligation. -/
theorem source (input logical : Slice U8) (row nextRow tag : U8) (size src dst : Usize)
    (inputLength : input.val.length=7015) (full : logical.val.length=14759)
    (bound : row.val<27) (next : nextRow.val=row.val+1)
    (shape : r1_wire.row_shape row=ok (some (tag,size)))
    (sourcePos : src.val=JFw_Geometry.sourcePos row.val)
    (destPos : dst.val=JFw_Geometry.destPos row.val) :
    ∃ semantic nextSrc nextDst,
      compact.expand_semantic_loop.body nativeValues input (iter row)
        (NBR_ProducerBuffers.semanticInitial logical) src dst =
          ok (.cont (iter nextRow,semantic,nextSrc,nextDst)) ∧
      nextSrc.val=JFw_Geometry.sourcePos nextRow.val ∧
      nextDst.val=JFw_Geometry.destPos nextRow.val ∧
      (restore logical semantic).val=semantic.val++logical.val.drop 13831 ∧
      (restore logical semantic).val.length=14759 ∧
      (restore logical semantic).val.drop 13831=logical.val.drop 13831 := by
  have initialSize : (NBR_ProducerBuffers.semanticInitial logical).val.length=13831 :=
    NBR_RangeGeometry.length logical 0#usize 13831#usize 13831 (by scalar_tac)
      (by change 13831≤_;omega)
  obtain ⟨semantic,nextSrc,nextDst,call,semLength,source,dest⟩ :=
    NBR_SemanticStep.source input (NBR_ProducerBuffers.semanticInitial logical)
      row nextRow tag size src dst bound next shape inputLength initialSize sourcePos destPos
  have restored : (restore logical semantic).val=semantic.val++logical.val.drop 13831 :=
    NCA_SemanticRestore.source logical semantic full semLength
  refine ⟨semantic,nextSrc,nextDst,call,source,dest,restored,(length _ _).trans full,?_⟩
  rw [restored,←semLength,List.drop_left]

#print axioms length
#print axioms source
end AspisR1.NCA_FullCarrierRow
