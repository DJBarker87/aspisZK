import NDO_JHa_Circle5
import NDO_JGw_Line5
import NDO_JHa_Accumulate
import NDO_JGc_TX2_QueryForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Query5
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
abbrev ops := JGc_TX2_QueryDictionary.ops JGp_Seeds.query
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 5
abbrev lineValue := JGw_Line5.value inverse
def node : U32 := Classical.choose (JFv_TX2_NodeCall.source (JGp_Rows.value 5).lineZ)

theorem source (p : verifier.Prepared) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (old : S8OwnedP6Finish.Weights) (sum : Sum)
    (queries : p.queries=JFq_Queries.value) (alpha : p.alpha=JFo_Prepared.value.alpha)
    (next : a.next=5#usize) (size : a.weights.val.length=64)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (crho : Port3_FlushInstall.Canonical p.rho)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress 5 0 (Port3_RowsInstall.toBW b)) :
    ∃ out after sumOut,
      verifier.candidate.query_values ops JFx_NativeBytes.proof p a JFr_TX2_Powers.value none
        (JGp_Geometry.value () JGp_Seeds.geometry) b=ok (.Ok (out,after)) ∧
      out.weights=a.weights ∧ out.next.val=6 ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power ∧
      PushTrace old (Port3_RowsInstall.toBW after) sumOut ∧ Progress 6 0 (Port3_RowsInstall.toBW after) := by
  have canonical : Port4C_QueryArithmetic.CanonE lineValue :=
    (Classical.choose_spec (JGw_Line5.source inverse)).2
  obtain ⟨out,after,sumOut,accumulated,weights,inc,cr,cp,ht,hp⟩ :=
    JHa_Accumulate.source (JGc_TX2_QueryDictionary.input JGp_Seeds.query) p old a b sum 5
      node lineValue size (by rw [next];decide) (by decide) crhs cpower crho canonical history phase
  refine ⟨out,after,sumOut,?_,weights,?_,cr,cp,ht,hp⟩
  · have fields := JGc_TX2_QueryDictionary.fields JGp_Seeds.query
    have nodeCall : JFv_TX2_NodeCall.sourceCall (JGp_Rows.value 5).lineZ=ok node :=
      (Classical.choose_spec (JFv_TX2_NodeCall.source (JGp_Rows.value 5).lineZ)).1
    unfold JFv_TX2_NodeCall.sourceCall at nodeCall
    obtain ⟨sq,hsq,nodeCall⟩ := Port3_PushFrame.bind_success _ _ _ nodeCall
    obtain ⟨dbl,hdbl,hnode⟩ := Port3_PushFrame.bind_success _ _ _ nodeCall
    apply JGc_TX2_QueryForward.source
    refine {
      query := JGp_Rows.query 5
      opening := JFo_Opening.value ⟨5,by decide⟩
      dots := JGw_Dots5.value
      inverse := inverse
      alpha0 := JFq_Alpha0.scalar
      alpha1 := JFq_Alpha1.scalar
      folded := JHa_Circle5.selected
      value := lineValue
      values := JGw_Values5.value
      selected := JHa_Circle5.selected
      u := UScalar.cast .Usize (JGp_Rows.query 5)
      z := (JGp_Rows.value 5).lineZ
      square := sq
      doubled := dbl
      one := 1#u32
      node := node
      query_read := ?_
      cast := rfl
      opening_read := ?_
      dots_read := ?_
      inverse_read := ?_
      alpha0_read := ?_
      circle := ?_
      values_read := ?_
      selected_read := ?_
      comparison := ?_
      alpha1_read := ?_
      line := ?_
      z_read := ?_
      square_call := hsq
      double_call := hdbl
      one_call := rfl
      node_call := hnode
      accumulate := accumulated
      marked := ?_ }
    · rw [queries,next];rfl
    · rw [fields.1,next];exact JFo_Opening.call ⟨5,by decide⟩
    · rw [fields.2.2.1];exact JGw_Dots5.source
    · rw [fields.2.1,next];exact JGw_Inverses.read () JGp_Seeds.geometry 5
    · rw [alpha];rfl
    · rw [fields.2.2.2.1];exact JHa_Circle5.source
    · exact JGw_Values5.source (JGc_TX2_QueryDictionary.input JGp_Seeds.query)
    · refine ⟨1#usize,?_,?_⟩
      · have hv : (UScalar.cast .Usize (JGp_Rows.query 5)).val=192317 := by
          change (UScalar.cast .Usize 192317#u32).val=192317
          scalar_tac
        simpa only [hv] using CheckpointBytesArithmetic.rem_four (UScalar.cast .Usize (JGp_Rows.query 5))
      · rfl
    · rw [fields.2.2.2.2.2.1];exact JGc_TX2_QueryDictionary.neSelf _
    · rw [alpha];rfl
    · rw [fields.2.2.2.2.1];exact JGw_Line5.returned inverse
    · rw [next];exact (Classical.choose_spec (JGw_GeometryReads.source () JGp_Seeds.geometry 5)).2.1
    · rw [fields.2.2.2.2.2.2.2];rfl
  · rw [next] at inc
    exact inc
#print axioms source
end AspisR1.JHa_Query5
end
