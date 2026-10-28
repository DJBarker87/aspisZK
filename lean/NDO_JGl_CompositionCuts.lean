import NDO_JGl_ConcreteOpenings
import NDO_JGl_BoxedNumeric
import NDO_JGl_SopsNumeric
import NDO_JGl_SemanticNumeric
import RPv_FIw_CompositionOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_CompositionCuts
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical decoded)
open pool_v1.pair_forest_semantic_terminal
attribute [local irreducible] JGl_ConcreteSelected.data JGl_NumericData.a JGl_NumericData.b
  JGl_NumericData.c JGl_NumericData.selectors JGl_NumericData.sops JGl_NumericData.semantic
/-- Invert the SAME successful actual composition and its SAME selected
constructor. No independently successful evaluator/semantic/copy call is assumed. -/
theorem value (selected : Array field.QM31 84#usize)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (comp g h active : field.QM31) (hs : canonical selected)
    (gather : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      JGl_SelectedCells.builder field.QM31.ZERO JFu_TerminalCallback.claims=ok selected)
    (run : composition_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi JFu_TerminalPrefix.challenges.theta=
        ok (.Ok (comp,c1,mask,g,h,active))) :
    c1=JGl_NumericData.a ∧
    ∃ (pos : Array field.QM31 4#usize)
      (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1),
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected JGl_NumericData.openings JGl_NumericData.sops=ok pos ∧
      semantic_packed JFu_PublicSemantic.value JGl_NumericData.openings JGl_NumericData.selectors=ok JGl_NumericData.semantic ∧
      pool_v1.pair_forest_copy_terminal.evaluate_with_selectors JGl_NumericData.a h JGl_NumericData.selectors
        JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
        JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index .PrivateTransfer=ok copy ∧
      copy.active=active := by
  have es := JGl_ConcreteSelected.value selected gather
  rw [es] at hs run
  obtain ⟨a,b,c,s,ps,variant,sem,pos,prepared,middle,copy,it,it1,
    same,r0,r1,r2,rs,rsp,rpos,rsem,rv,rc,rp,rit,rit1,rm,rf,ra⟩ :=
    FIw_CompositionOrigins.reached JFu_PublicSemantic.value JGl_ConcreteSelected.data JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi JFu_TerminalPrefix.challenges.theta
      comp g h active c1 mask run
  have ea := JGl_ConcreteOpenings.a a hs r0
  have eb := JGl_ConcreteOpenings.b b hs r1
  have ec := JGl_ConcreteOpenings.c c hs r2
  rw [ea] at same rpos rsem rc
  rw [eb,ec] at rpos rsem
  have es := JGl_BoxedNumeric.value s rs
  rw [es] at rsp rsem rc
  have ep := JGl_SopsNumeric.value ps rsp
  rw [ep] at rpos
  have em := JGl_SemanticNumeric.source sem rsem
  rw [em] at rsem
  have vcall : copy_variant JFu_PublicSemantic.value.variant=ok
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer := rfl
  have ev := Result.ok.inj (rv.symm.trans vcall)
  rw [ev] at rc
  exact ⟨same,pos,copy,rpos,rsem,rc,ra⟩
#print axioms value
end AspisR1.JGl_CompositionCuts
end
