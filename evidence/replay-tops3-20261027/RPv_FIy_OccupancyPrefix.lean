import RPv_FIy_OccupancyLoop
import RPv_FIw_ScalarArithmetic
import RPv_FIx_ArrayMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyPrefix
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)

def run (input_occupancy output_occupancy : NQ) (opened : Array NQ 16#usize) :
    Result (NQ × NQ × NQ × Array NQ 12#usize) := do
  let occupied ← Array.index_usize opened 0#usize
  let inverse ← Array.index_usize opened 1#usize
  let one_minus ← field.QM31.sub field.QM31.ONE occupied
  let occupancy := Array.repeat 12#usize field.QM31.ZERO
  let both ← field.QM31.add input_occupancy output_occupancy
  let q ← field.QM31.sub occupied field.QM31.ONE
  let q1 ← field.QM31.mul occupied q
  let q2 ← field.QM31.mul both q1
  let occupancy1 ← Array.update occupancy 0#usize q2
  let q3 ← Array.index_usize opened 9#usize
  let q4 ← field.QM31.mul q3 inverse
  let q5 ← field.QM31.sub q4 occupied
  let q6 ← field.QM31.mul both q5
  let occupancy2 ← Array.update occupancy1 1#usize q6
  let q7 ← field.QM31.mul one_minus inverse
  let q8 ← field.QM31.mul both q7
  let a ← Array.update occupancy2 2#usize q8
  ok (occupied,one_minus,both,a)

def model (input output : K) (opened : Nat → K) : Fin (12#usize).val → K :=
  Function.update (Function.update (Function.update (fun _=>0)
    ⟨0,by decide⟩ ((input+output)*(opened 0*(opened 0-1))))
    ⟨1,by decide⟩ ((input+output)*(opened 9*opened 1-opened 0)))
    ⟨2,by decide⟩ ((input+output)*((1-opened 0)*opened 1))

theorem value (input output : NQ) (opened : Array NQ 16#usize)
    (occupied oneMinus both : NQ) (a : Array NQ 12#usize)
    (hi : Canon input) (ho : Canon output) (ha : canonical opened)
    (success : run input output opened=ok (occupied,oneMinus,both,a)) :
    Canon occupied ∧ Canon oneMinus ∧ Canon both ∧ canonical a ∧
      decode occupied=FIv_NativeArray.value opened 0 ∧
      decode oneMinus=1-FIv_NativeArray.value opened 0 ∧
      decode both=decode input+decode output ∧
      decoded a=model (decode input) (decode output) (FIv_NativeArray.value opened) := by
  unfold run at success
  obtain ⟨occ,h_occ,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨inverse,h_inverse,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨m,h_m,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨b,h_b,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q,h_q,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,h_q1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,h_q2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨occupancy1,h_occupancy1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q3,h_q3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q4,h_q4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q5,h_q5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q6,h_q6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨occupancy2,h_occupancy2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q7,h_q7,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q8,h_q8,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨a1,h_a1,success⟩ := FIv_Map.bind_success _ _ _ success
  cases Result.ok.inj success
  have cocc := FIv_NativeArray.canonical opened 0#usize occupied ha h_occ
  have cinv := FIv_NativeArray.canonical opened 1#usize inverse ha h_inverse
  have cm := FIv_SubMap.qm field.QM31.ONE occupied oneMinus FIv_NativeValue.one.1 cocc h_m
  have cb := FIv_NativeValue.add input output both hi ho h_b
  have cq := FIv_SubMap.qm occupied field.QM31.ONE q cocc FIv_NativeValue.one.1 h_q
  have cq1 := FIv_NativeValue.mul occupied q q1 cocc cq.1 h_q1
  have cq2 := FIv_NativeValue.mul both q1 q2 cb.1 cq1.1 h_q2
  have zero : canonical (Array.repeat 12#usize field.QM31.ZERO) := by
    intro x hx
    have e : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    rw [e]
    exact FIv_NativeValue.zero.1
  have u1 := FIw_ArrayValue.update _ occupancy1 0#usize q2 (by decide) zero cq2.1 h_occupancy1
  have cq3 := FIv_NativeArray.canonical opened 9#usize q3 ha h_q3
  have cq4 := FIv_NativeValue.mul q3 inverse q4 cq3 cinv h_q4
  have cq5 := FIv_SubMap.qm q4 occupied q5 cq4.1 cocc h_q5
  have cq6 := FIv_NativeValue.mul both q5 q6 cb.1 cq5.1 h_q6
  have u2 := FIw_ArrayValue.update occupancy1 occupancy2 1#usize q6 (by decide) u1.1 cq6.1 h_occupancy2
  have cq7 := FIv_NativeValue.mul oneMinus inverse q7 cm.1 cinv h_q7
  have cq8 := FIv_NativeValue.mul both q7 q8 cb.1 cq7.1 h_q8
  have u3 := FIw_ArrayValue.update occupancy2 a 2#usize q8 (by decide) u2.1 cq8.1 h_a1
  refine ⟨cocc,cm.1,cb.1,u3.1,?_,?_,cb.2,?_⟩
  · exact (FIv_NativeArray.read opened 0#usize occupied h_occ).symm
  · rw [cm.2,FIv_NativeValue.one.2,←FIv_NativeArray.read opened 0#usize occupied h_occ]
    rfl
  · rw [u3.2,u2.2,u1.2,cq8.2,cq7.2,cq6.2,cq5.2,cq4.2,cq2.2,cq1.2,cq.2,
      cb.2,cm.2,FIv_NativeValue.one.2,FIx_ArrayMeaning.decoded_repeat,FIv_NativeValue.zero.2,
      ←FIv_NativeArray.read opened 0#usize occupied h_occ,
      ←FIv_NativeArray.read opened 1#usize inverse h_inverse,
      ←FIv_NativeArray.read opened 9#usize q3 h_q3]
    rfl
#print axioms value
end AspisR1.FIy_OccupancyPrefix
end
