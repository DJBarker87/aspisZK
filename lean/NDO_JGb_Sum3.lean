import NDO_JGb_Sum3Outer
import NDO_JGb_Sum3Converter
import RPv_AspisR1_PoseidonPreparedSum3ActualValue
import RPv_JFy_PreparedSteps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_Sum3
open Aeneas Aeneas.Std Result FIq_Native
open FIv_Map (map map_bind map_ok)
open FIv_NativeArithmetic (NQ qm)
open FIv_PreparedNew (NP prepared)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
theorem mapped (left : Array NP 3#usize) (right : Array NQ 3#usize) :
    map qm (field.qm31_sum_products3_prepared left right)=
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared
      (JGb_ArrayMap.array prepared left) (JGb_ArrayMap.array qm right) := by
  unfold field.qm31_sum_products3_prepared AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared
  dsimp only
  simp only [map_bind]
  let sums : JGb_Sum3Channel.Sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
  have outer := JGb_Sum3Outer.mapped 3 (⟨0#usize,3#usize⟩ : core.ops.range.Range Usize) left right sums (by rfl)
  exact (congrArg (fun r : Result JGb_Sum3Channel.Sums => do
      let s ← r
      map qm (field.qm31_from_karatsuba_channel_sums s)) outer).trans
    (by simp only [JGb_Sum3Converter.mapped];rfl)
#print axioms mapped

theorem source (left : Array NP 3#usize) (right : Array NQ 3#usize)
    (hl : ∀ p∈left.val,JFy_PreparedSteps.Valid p) (hr : canonical right) :
    ∃ out,field.qm31_sum_products3_prepared left right=ok out ∧ Canon out := by
  have hp : ∀ i : Fin 3,∃ x : AspisR1SelectedMaskProbe.field.QM31,
      ExtractedMaskTowerAdd.CanonicalQM x ∧
      ExtractedMaskPreparedState.PreparedFor
        ((JGb_ArrayMap.array prepared left).val[i.val]'(by simp only [JGb_ArrayMap.array,List.length_map,left.property];change i.val<3;exact i.isLt)) x := by
    intro i
    obtain ⟨theta,ht,hprep⟩ := hl (left.val[i.val]'(by rw [left.property];exact i.isLt)) (List.getElem_mem _)
    simp only [JGb_ArrayMap.array,List.getElem_map]
    exact ⟨qm theta,ht,hprep⟩
  have hright : ∀ i : Fin 3, ExtractedMaskQM31Exact.CurrentCanonicalQM
      ((JGb_ArrayMap.array qm right).val[i.val]'(by simp only [JGb_ArrayMap.array,List.length_map,right.property];change i.val<3;exact i.isLt)) := by
    intro i
    simp only [JGb_ArrayMap.array,List.getElem_map]
    exact hr _ (List.getElem_mem (by rw [right.property];exact i.isLt))
  obtain ⟨out,x0,x1,x2,call,hcan,_⟩ := PoseidonPreparedSum3ActualValue.actual_sum3_value
    (JGb_ArrayMap.array prepared left) (JGb_ArrayMap.array qm right) hp hright
  have same := mapped left right
  rw [call] at same
  cases run : field.qm31_sum_products3_prepared left right with
  | fail e => rw [run] at same;cases same
  | div => rw [run] at same;cases same
  | ok out1 =>
    rw [run,map_ok] at same
    have eq := Result.ok.inj same
    exact ⟨out1,rfl,by change ExtractedMaskQM31Exact.CurrentCanonicalQM (qm out1);rw [eq];exact hcan⟩
#print axioms source
end AspisR1.JGb_Sum3
end
