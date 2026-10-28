import NDO_JGp_PrepareLayout
import NDO_JGp_Allocation
import NDO_JGp_PrepareReads
import NDO_JGp_RecombinedReads
set_option autoImplicit false
namespace AspisR1.JGp_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge FirstComposition
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes List.replicate

theorem total : (13831#usize + 928#usize : Result Usize)=ok 14759#usize := by
  apply UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms total

theorem inhabited {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    let ops := JGp_PrepareLayout.installed (JGp_Allocation.base base) query geo
    let D0 := F3V_OracleDictionary.current JFp_SHADigest.digest D
    ∃ (out : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize),
      verifier.candidate.prepare ops D0 (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof hash none input=ok (.Ok out,scratch) := by
  dsimp only
  let ops := JGp_PrepareLayout.installed (JGp_Allocation.base base) query geo
  let D0 := F3V_OracleDictionary.current JFp_SHADigest.digest D
  obtain ⟨expanded,pre,view,sem,out,scratch,expand,parse,yexpand,wide,semantic,prepared⟩ :=
    JGn_CurrentPreparation.inhabited D hash input
  have hs : expanded.length=13831 :=
    (AspisS1NativeCompactLengths.semantic_length AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored JFw_RealExpansion.initial expanded (.Ok ()) expand).trans JFw_RealExpansion.initial_length
  have hy := JGe_Payload27.length
  have viewsem := sourceView_semantic _ _ _ _ wide
  have readSemantic := JGp_RecombinedReads.semantic expanded JGe_Payload27.value hs hy
  have readY1 := JGp_RecombinedReads.y1 expanded JGe_Payload27.value hs hy
  have allocation : ops.op1 core.marker.CopyU8 14759#usize 0#u8=ok (.Ok JGp_Allocation.buffer) :=
    JGp_Allocation.allocated
  have expandCall : ops.op10 JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) := expand
  have yCall : ops.op11 JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),JGe_Payload27.value) := yexpand
  have viewCall : ops.op5 JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) := wide
  have semCall : ops.op9 D0 (toCurrentPublic JFs_PublicSerialization.value) view.semantic hash none=ok (.Ok sem) := by
    rw [viewsem]
    exact semantic
  have newCall : ops.op8 D0 sem view hash input=ok (.Ok out,scratch) := prepared
  refine ⟨out,scratch,?_⟩
  unfold verifier.candidate.prepare
  rw [JGp_PrepareLayout.logical,bind_tc_ok,JGp_PrepareLayout.y1,bind_tc_ok,total,bind_tc_ok,allocation,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,alloc.vec.Vec.deref_mut]
  erw [JGn_PrepareBuffer.split,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  erw [JGp_PrepareLayout.semantic,bind_tc_ok,JGp_PrepareLayout.offsetY1,bind_tc_ok,
    JGp_PrepareReads.semantic,bind_tc_ok,expandCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  erw [JGp_PrepareLayout.inactive,bind_tc_ok,JGp_PrepareReads.y1,bind_tc_ok,yCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  erw [readSemantic,bind_tc_ok,readY1,bind_tc_ok,viewCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [semCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,verifier.mark]
  exact newCall
#print axioms inhabited
end AspisR1.JGp_Prepare
