import NDO_JGn_CopyNumeric
import NDO_JGn_PoseidonNumeric
import NDO_JGl_CompositionCuts
import NDO_FIv_FoldsTotal
import NDO_JGb_Challenges
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CompositionValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem value (selected : Array field.QM31 84#usize)
    (a : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (comp g active : field.QM31) (hs : canonical selected)
    (gather : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      JGl_SelectedCells.builder field.QM31.ZERO JFu_TerminalCallback.claims=ok selected)
    (run : composition_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi JFu_TerminalPrefix.challenges.theta=
      ok (.Ok (comp,a,mask,g,JGn_CopyNumeric.helper,active))) :
    decode comp=FIv_CompositionValue.polynomial (decode JFu_TerminalPrefix.challenges.theta)
      JGl_NumericData.semantic JGl_NumericData.poseidon JGn_CopyNumeric.residual ∧
    active=JGn_ActiveData.a64 := by
  have es := JGl_ConcreteSelected.value selected gather
  rw [es] at hs run
  obtain ⟨x,y,z,s,ps,variant,sem,pos,prepared,middle,copy,it,it1,
    same,r0,r1,r2,rs,rsp,rpos,rsem,rv,rc,rp,rit,rit1,rm,rf,ra⟩ :=
    FIw_CompositionOrigins.reached JFu_PublicSemantic.value JGl_ConcreteSelected.data JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi JFu_TerminalPrefix.challenges.theta
      comp g JGn_CopyNumeric.helper active a mask run
  have ex := JGl_ConcreteOpenings.a x hs r0
  have ey := JGl_ConcreteOpenings.b y hs r1
  have ez := JGl_ConcreteOpenings.c z hs r2
  rw [ex] at rpos rsem rc
  rw [ey,ez] at rpos rsem
  have sel := JGl_BoxedNumeric.value s rs
  rw [sel] at rsp rsem rc
  have sop := JGl_SopsNumeric.value ps rsp
  rw [sop] at rpos
  have semEq := JGl_SemanticNumeric.source sem rsem
  have posEq := JGn_PoseidonNumeric.identified pos rpos
  have variantCall : copy_variant JFu_PublicSemantic.value.variant=ok
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer := rfl
  have ev := Result.ok.inj (rv.symm.trans variantCall)
  rw [ev] at rc
  have cv := JGn_CopyNumeric.identified copy rc
  rw [semEq] at rit
  rw [posEq] at rit1
  have eit : it=⟨JGl_NumericData.semantic.val⟩ := by cases it;cases rit;rfl
  have eit1 : it1=⟨JGl_NumericData.poseidon.val⟩ := by cases it1;cases rit1;rfl
  rw [eit,cv.1] at rm
  rw [eit1] at rf
  have actual : FIv_FoldsTotal.body JGl_NumericData.semantic JGl_NumericData.poseidon
      JFu_TerminalPrefix.challenges.theta JGn_CopyNumeric.residual=ok comp := by
    unfold FIv_FoldsTotal.body
    rw [rp,bind_tc_ok,rm,bind_tc_ok,rf]
  obtain ⟨out,called,hc,hv⟩ := FIv_FoldsTotal.value JGl_NumericData.semantic JGl_NumericData.poseidon
    JFu_TerminalPrefix.challenges.theta JGn_CopyNumeric.residual JGb_Challenges.theta
    JGn_CopyNumeric.residualCanonical JGl_NumericCanonical.semantic JGl_NumericCanonical.poseidon
  have equal := Result.ok.inj (called.symm.trans actual)
  exact ⟨equal ▸ hv,ra.symm.trans cv.2⟩
#print axioms value
end AspisR1.JGn_CompositionValue
end
