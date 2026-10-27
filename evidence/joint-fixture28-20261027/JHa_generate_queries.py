from pathlib import Path
import sys
import re
R=Path(__file__).resolve().parents[2]
for i in range(10):
 qword=int(re.search(rf'theorem word{i} :.*?=([0-9]+)#u32',(R/'lean/JFq_QueryWords.lean').read_text())[1])
 idx=qword%4
 s=f'''import JHa_Circle{i}
import JGw_Line{i}
import JHa_Accumulate
import JGc_TX2_QueryForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Query{i}
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
abbrev ops := JGc_TX2_QueryDictionary.ops JGp_Seeds.query
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry {i}
abbrev lineValue := JGw_Line{i}.value inverse
def node : U32 := Classical.choose (JFv_TX2_NodeCall.source (JGp_Rows.value {i}).lineZ)

theorem source (p : verifier.Prepared) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (old : S8OwnedP6Finish.Weights) (sum : Sum)
    (queries : p.queries=JFq_Queries.value) (alpha : p.alpha=JFo_Prepared.value.alpha)
    (next : a.next={i}#usize) (size : a.weights.val.length=64)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (crho : Port3_FlushInstall.Canonical p.rho)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress {i} 0 (Port3_RowsInstall.toBW b)) :
    ∃ out after sumOut,
      verifier.candidate.query_values ops JFx_NativeBytes.proof p a JFr_TX2_Powers.value none
        (JGp_Geometry.value () JGp_Seeds.geometry) b=ok (.Ok (out,after)) ∧
      out.weights=a.weights ∧ out.next.val={i+1} ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power ∧
      PushTrace old (Port3_RowsInstall.toBW after) sumOut ∧ Progress {i+1} 0 (Port3_RowsInstall.toBW after) := by
  have canonical : Port4C_QueryArithmetic.CanonE lineValue :=
    (Classical.choose_spec (JGw_Line{i}.source inverse)).2
  obtain ⟨out,after,sumOut,accumulated,weights,inc,cr,cp,ht,hp⟩ :=
    JHa_Accumulate.source (JGc_TX2_QueryDictionary.input JGp_Seeds.query) p old a b sum {i}
      node lineValue size (by rw [next];decide) (by decide) crhs cpower crho canonical history phase
  refine ⟨out,after,sumOut,?_,weights,?_,cr,cp,ht,hp⟩
  · have fields := JGc_TX2_QueryDictionary.fields JGp_Seeds.query
    have nodeCall : JFv_TX2_NodeCall.sourceCall (JGp_Rows.value {i}).lineZ=ok node :=
      (Classical.choose_spec (JFv_TX2_NodeCall.source (JGp_Rows.value {i}).lineZ)).1
    unfold JFv_TX2_NodeCall.sourceCall at nodeCall
    obtain ⟨sq,hsq,nodeCall⟩ := Port3_PushFrame.bind_success _ _ _ nodeCall
    obtain ⟨dbl,hdbl,hnode⟩ := Port3_PushFrame.bind_success _ _ _ nodeCall
    apply JGc_TX2_QueryForward.source
    refine {{
      query := JGp_Rows.query {i}
      opening := JFo_Opening.value ⟨{i},by decide⟩
      dots := JGw_Dots{i}.value
      inverse := inverse
      alpha0 := JFq_Alpha0.scalar
      alpha1 := JFq_Alpha1.scalar
      folded := JHa_Circle{i}.selected
      value := lineValue
      values := JGw_Values{i}.value
      selected := JHa_Circle{i}.selected
      u := UScalar.cast .Usize (JGp_Rows.query {i})
      z := (JGp_Rows.value {i}).lineZ
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
      marked := ?_ }}
    · rw [queries,next];rfl
    · rw [fields.1,next];exact JFo_Opening.call ⟨{i},by decide⟩
    · rw [fields.2.2.1];exact JGw_Dots{i}.source
    · rw [fields.2.1,next];exact JGw_Inverses.read () JGp_Seeds.geometry {i}
    · rw [alpha];rfl
    · rw [fields.2.2.2.1];exact JHa_Circle{i}.source
    · exact JGw_Values{i}.source (JGc_TX2_QueryDictionary.input JGp_Seeds.query)
    · refine ⟨{idx}#usize,?_,?_⟩
      · have hv : (UScalar.cast .Usize (JGp_Rows.query {i})).val={qword} := by
          change (UScalar.cast .Usize {qword}#u32).val={qword}
          scalar_tac
        simpa only [hv] using CheckpointBytesArithmetic.rem_four (UScalar.cast .Usize (JGp_Rows.query {i}))
      · rfl
    · rw [fields.2.2.2.2.2.1];exact JGc_TX2_QueryDictionary.neSelf _
    · rw [alpha];rfl
    · rw [fields.2.2.2.2.1];exact JGw_Line{i}.returned inverse
    · rw [next];exact (Classical.choose_spec (JGw_GeometryReads.source () JGp_Seeds.geometry {i})).2.1
    · rw [fields.2.2.2.2.2.2.2];rfl
  · rw [next] at inc
    exact inc
#print axioms source
end AspisR1.JHa_Query{i}
end
'''
 dst=R/f'lean/JHa_Query{i}.lean'
 if '--check' in sys.argv: assert dst.read_text()==s,str(dst)
 else: dst.write_text(s)
