import NBR_SemanticReturn
import NBR_ValuesPort
import JFw_Row
import JFw_Geometry
set_option autoImplicit false
namespace AspisR1.NBR_SemanticStep
open Aeneas Aeneas.Std Result WP ControlFlow
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator

/-- ONE semantic row on an arbitrary live model pre-state. Every values-leaf
and slice precondition is derived from the source loop's geometry invariant.
JFw supplies the existing step proof; this exports its exact association. -/
theorem source (input out : Slice U8) (row nextRow tag : U8) (size src dst : Usize)
    (bound : row.val<27) (next : nextRow.val=row.val+1)
    (shape : r1_wire.row_shape row=ok (some (tag,size)))
    (inputLength : input.length=7015) (outLength : out.length=13831)
    (sourcePos : src.val=JFw_Geometry.sourcePos row.val)
    (destPos : dst.val=JFw_Geometry.destPos row.val) :
    ∃ updated nextSrc nextDst,
      compact.expand_semantic_loop.body nativeValues input (iter row) out src dst=
        ok (.cont (iter nextRow,updated,nextSrc,nextDst)) ∧
      updated.length=13831 ∧
      nextSrc.val=JFw_Geometry.sourcePos nextRow.val ∧
      nextDst.val=JFw_Geometry.destPos nextRow.val := by
  have sizeEq : size.val=(OraclePortCompactDraft.rowShape row.val).2 :=
    congrArg Prod.snd (PSem_Shapes.valid_shape row tag size bound shape)
  obtain ⟨sb,aligned,sp,dp,ib,ob⟩ := JFw_Geometry.step row.val bound
  obtain ⟨result,call,buf,s,d,resultEq,sValue,dValue⟩ :=
    spec_imp_exists (JFw_Row.spec input out row nextRow tag size src dst bound next shape
      (by omega) (by omega) (by rw [sourcePos,sizeEq,inputLength,←sp];exact ib)
      (by rw [destPos,sizeEq,outLength,←dp];exact ob) (by omega) (by omega))
  subst result
  have length := AspisS1NativeCompactLengths.body_length nativeValues input out (iter row) src dst _ call
  refine ⟨buf,s,d,call,length.trans outLength,?_,?_⟩
  · rw [sValue,sourcePos,sizeEq,←sp,next]
  · rw [dValue,destPos,sizeEq,←dp,next]

#print axioms source
end AspisR1.NBR_SemanticStep
