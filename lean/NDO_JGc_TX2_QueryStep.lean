import NDO_JGc_TX2_QueryReads
import NDO_JGc_TX2_QueryForward
import NDO_JFz_TX2_ChainStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_QueryStep
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

theorem source {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Ops) (i : Fin 12) (a out : verifier.Accumulator)
    (b bout : verifier.BatchedWeights)
    (next : a.next=JFv_TX2_GeometryReads.cursor i)
    (accumulated : verifier.accumulate_batched_with_node (JGc_TX2_QueryDictionary.ops seed)
      JFo_Prepared.value a (JFz_TX2_Nodes.value i) (JFz_TX2_Gates.lineValue i) b=ok (out,bout)) :
    verifier.candidate.query_values (JGc_TX2_QueryDictionary.ops seed)
      JFx_NativeBytes.proof JFo_Prepared.value a JFr_TX2_Powers.value none
      (JFv_TX2_Geometry.value err geometrySeed) b=ok (.Ok (out,bout)) := by
  let ops := JGc_TX2_QueryDictionary.ops seed
  have fields := JGc_TX2_QueryDictionary.fields seed
  have node := JFz_TX2_Nodes.source i
  unfold JFv_TX2_NodeCall.sourceCall at node
  obtain ⟨sq,hsq,node⟩ := Port3_PushFrame.bind_success _ _ _ node
  obtain ⟨dbl,hdbl,hnode⟩ := Port3_PushFrame.bind_success _ _ _ node
  apply JGc_TX2_QueryForward.source
  refine {
    query := JFv_TX2_Rows.query i
    opening := JFo_Opening.value (JFn_Values.position i)
    dots := JFs_TX2_Dots.value i
    inverse := JFv_TX2_CircleGeometry.inverse err geometrySeed i
    alpha0 := JFq_Alpha0.scalar
    alpha1 := JFq_Alpha1.scalar
    folded := JFz_TX2_Gates.selected i
    value := JFz_TX2_Gates.lineValue i
    values := JFn_Values.value i
    selected := JFz_TX2_Gates.selected i
    u := UScalar.cast .Usize (JFv_TX2_Rows.query i)
    z := (JFv_TX2_Rows.value i).lineZ
    square := sq
    doubled := dbl
    one := 1#u32
    node := JFz_TX2_Nodes.value i
    query_read := ?_
    cast := rfl
    opening_read := ?_
    dots_read := ?_
    inverse_read := ?_
    alpha0_read := JGc_TX2_QueryReads.alpha0
    circle := ?_
    values_read := ?_
    selected_read := ⟨JGc_TX2_QueryReads.selector i,JGc_TX2_QueryReads.remainder i,JGc_TX2_QueryReads.selected i⟩
    comparison := ?_
    alpha1_read := JGc_TX2_QueryReads.alpha1
    line := ?_
    z_read := ?_
    square_call := hsq
    double_call := hdbl
    one_call := rfl
    node_call := hnode
    accumulate := accumulated
    marked := ?_ }
  · rw [next];exact JGc_TX2_QueryReads.query i
  · rw [fields.1,next];exact JGc_TX2_QueryReads.opening i
  · rw [fields.2.2.1];exact JFs_TX2_Dots.adapter i
  · rw [fields.2.1,next];exact JFv_TX2_CircleGeometry.read err geometrySeed i
  · rw [fields.2.2.2.1];exact JFz_TX2_Gates.circle err geometrySeed i
  · exact JFn_Values.source (JGc_TX2_QueryDictionary.input seed) i
  · rw [fields.2.2.2.2.2.1];exact JGc_TX2_QueryDictionary.neSelf _
  · rw [fields.2.2.2.2.1];exact JFz_TX2_Gates.line err geometrySeed i
  · rw [next];exact (Classical.choose_spec (JFv_TX2_GeometryReads.source err geometrySeed i)).2.1
  · rw [fields.2.2.2.2.2.2.2];rfl
#print axioms source
end AspisR1.JGc_TX2_QueryStep
end
