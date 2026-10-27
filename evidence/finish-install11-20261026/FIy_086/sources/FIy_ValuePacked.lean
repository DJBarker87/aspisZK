import FIy_ValueSelector
import FIy_ValueTail
import FIy_Scaling
import FIx_ConservationMeaning
import FIx_PreweightedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ValuePacked
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIy_ValueTail (Openings)
open FIy_FrontierStep (Selectors)

def selector (s : Selectors) : K :=
  ((0+FIy_ValueSelector.model s ⟨0,by decide⟩)+FIy_ValueSelector.model s ⟨1,by decide⟩)+
    FIy_ValueSelector.model s ⟨2,by decide⟩
def rangeModel (o : Openings) (s : Selectors) : Fin (33#usize).val → K := fun j=>
  selector s*FIy_ValueTail.model o (FIx_ValueBitPrefix.model o (fun _=>0)) j

def conservation (o : Openings) (s : Selectors) (j : Fin (2#usize).val) : K :=
  let sel := FIv_NativeArray.value s.high 63*FIv_NativeArray.value s.low 6
  if j.val=0 then sel*((FIv_NativeArray.value o.z 0-FIv_NativeArray.value o.z 1)-FIv_NativeArray.value o.z 2)
  else sel*(FIv_NativeArray.value o.succ_z 0-FIv_NativeArray.value o.succ_z 1)

theorem value (packed out : Array NQ 24#usize) (o : Openings) (s : Selectors)
    (hp : canonical packed) (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hh : canonical s.high) (hl : canonical s.low)
    (success : pool_v1.pair_forest_semantic_terminal.add_value_lanes packed o s=ok out) :
    canonical out ∧ ∀ j : Fin (24#usize).val,
      decoded out j=decoded packed j+FIx_SelectedMeaning.contribution (rangeModel o s) 49 j.val+
        FIx_SelectedMeaning.contribution (conservation o s) 82 j.val := by
  unfold pool_v1.pair_forest_semantic_terminal.add_value_lanes at success
  obtain ⟨value_selectors,h_value_selectors,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q,h_q,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,h_q1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,h_q2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q3,h_q3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q4,h_q4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range_selector,h_range_selector,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨openings1, range1⟩,h_openings1_range1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨openings2, range2⟩,h_openings2_range2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨openings3, range3⟩,h_openings3_range3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q5,h_q5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q6,h_q6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i,h_i,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q7,h_q7,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q8,h_q8,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q9,h_q9,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i1,h_i1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q10,h_q10,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨reconstructed,h_reconstructed,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q11,h_q11,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q12,h_q12,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range4,h_range4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q13,h_q13,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range5,h_range5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q14,h_q14,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range6,h_range6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨iter, into_iter_back⟩,h_iter_into_iter_back,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨im, back⟩,h_im_back,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨packed1,h_packed1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i2,h_i2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i3,h_i3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨conservation_selector,h_conservation_selector,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q15,h_q15,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q16,h_q16,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q17,h_q17,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q18,h_q18,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q19,h_q19,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q20,h_q20,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q21,h_q21,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q22,h_q22,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q23,h_q23,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q24,h_q24,success⟩ := FIv_Map.bind_success _ _ _ success
  have finalCall := success
  have zero : canonical (Array.repeat 33#usize field.QM31.ZERO) := by
    intro x hx
    have e : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    rw [e]
    exact FIv_NativeValue.zero.1
  have v0 := FIx_ValueBits0.value 10 0#usize o openings1 _ range1 (by rfl) hz zero h_openings1_range1
  have e0 := v0.1
  subst openings1
  have v1 := FIx_ValueBits1.value 10 0#usize o openings2 range1 range2 (by rfl) hs v0.2.1 h_openings2_range2
  have e1 := v1.1
  subst openings2
  have v2 := FIx_ValueBits2.value 10 0#usize o openings3 range2 range3 (by rfl) hx v1.2.1 h_openings3_range3
  have e2 := v2.1
  subst openings3
  have bitRun : FIx_ValueBitPrefix.calls o (Array.repeat 33#usize field.QM31.ZERO)=ok (o,range3) := by
    simp only [FIx_ValueBitPrefix.calls,h_openings1_range1,bind_tc_ok]
    change (do let (o2,r2) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 o range1 0#usize
               pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 o2 r2 0#usize)=ok (o,range3)
    rw [h_openings2_range2]
    exact h_openings3_range3
  have bitValue := FIx_ValueBitPrefix.value o o _ range3 hz hs hx zero bitRun
  have tailRun : FIy_ValueTail.run o range3=ok range6 := by
    simp only [FIy_ValueTail.run,h_q5,h_q6,h_i,h_q7,h_q8,h_q9,h_i1,h_q10,
      h_reconstructed,h_q11,h_q12,h_range4,h_q13,h_range5,h_q14,h_range6,bind_tc_ok]
  have tailValue := FIy_ValueTail.value o range3 range6 hz hs hx bitValue.2.1 tailRun
  have mapValue := FIy_ValueSelector.value s value_selectors hh hl h_value_selectors
  have cq := FIv_NativeArray.canonical value_selectors 0#usize q mapValue.1 h_q
  have a1 := FIv_NativeValue.add field.QM31.ZERO q q1 FIv_NativeValue.zero.1 cq h_q1
  have cq2 := FIv_NativeArray.canonical value_selectors 1#usize q2 mapValue.1 h_q2
  have a3 := FIv_NativeValue.add q1 q2 q3 a1.1 cq2 h_q3
  have cq4 := FIv_NativeArray.canonical value_selectors 2#usize q4 mapValue.1 h_q4
  have asel := FIv_NativeValue.add q3 q4 range_selector a3.1 cq4 h_range_selector
  have selValue : decode range_selector=selector s := by
    rw [asel.2,a3.2,a1.2,FIv_NativeValue.zero.2,
      FIw_ArrayReadValue.read value_selectors 0#usize (by decide) q h_q,
      FIw_ArrayReadValue.read value_selectors 1#usize (by decide) q2 h_q2,
      FIw_ArrayReadValue.read value_selectors 2#usize (by decide) q4 h_q4,mapValue.2]
    rfl
  let scaled := into_iter_back (back im)
  have scaleRun : FIy_ScaleReadback.run range6 range_selector=ok scaled := by
    unfold FIy_ScaleReadback.run
    simp only [h_iter_into_iter_back,bind_tc_ok]
    change (do let (im,b) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3 iter (fun x=>x) range_selector
               ok (into_iter_back (b im)))=ok scaled
    rw [h_im_back]
    rfl
  have scaledValue := FIy_Scaling.value range6 scaled range_selector tailValue.1 asel.1 scaleRun
  have scaledModel : decoded scaled=rangeModel o s := by
    rw [scaledValue.2,tailValue.2,bitValue.2.2,FIx_ArrayMeaning.decoded_repeat,FIv_NativeValue.zero.2,selValue]
    rfl
  have first := FIx_PreweightedMeaning.value packed packed1 49#usize scaled (rangeModel o s)
    scaledModel (by decide) (by decide) hp scaledValue.1 h_packed1
  let scalars := Array.make 2#usize [q20,q24]
  have scalarRun : FIx_ValueConservation.run conservation_selector o.z o.succ_z=ok scalars := by
    simp only [FIx_ValueConservation.run,h_q15,h_q16,h_q17,h_q18,h_q19,h_q20,h_q21,h_q22,h_q23,h_q24,bind_tc_ok]
    rfl
  have selectorValue := FIw_SelectorRow.value_exact s i3 conservation_selector hh hl h_conservation_selector
  have cv := FIx_ValueConservation.value conservation_selector o.z o.succ_z scalars selectorValue.1 hz hs scalarRun
  have rowValue := FIx_ConservationMeaning.index i2 i3 h_i2 h_i3
  have cm : decoded scalars=conservation o s := by
    apply FIx_ArrayMeaning.decoded_of_map
    rw [cv.2,selectorValue.2,rowValue]
    rfl
  have last := FIx_PreweightedMeaning.value packed1 out 82#usize scalars (conservation o s) cm
    (by decide) (by decide) first.1 cv.1 success
  refine ⟨last.1,?_⟩
  intro j
  rw [last.2 j,first.2 j]
  rfl
#print axioms value
end AspisR1.FIy_ValuePacked
end
