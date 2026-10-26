import FIy_ValueShifts
import FIx_ReconstructMeaning
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ValueTail
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings

def run (o : Openings) (range : Array NQ 33#usize) : Result (Array NQ 33#usize) := do
  let q5 ← pool_v1.pair_forest_semantic_terminal.reconstruct_10 o.z
  let q6 ←
    pool_v1.pair_forest_semantic_terminal.reconstruct_10 o.succ_z
  let i ← 1#u32 <<< 10#i32
  let q7 ← field.QM31.mul_m31 q6 i
  let q8 ← field.QM31.add q5 q7
  let q9 ←
    pool_v1.pair_forest_semantic_terminal.reconstruct_10 o.xor12_z
  let i1 ← 1#u32 <<< 20#i32
  let q10 ← field.QM31.mul_m31 q9 i1
  let reconstructed ← field.QM31.add q8 q10
  let q11 ← Array.index_usize o.z 10#usize
  let q12 ← field.QM31.sub q11 reconstructed
  let range4 ← Array.update range 30#usize q12
  let q13 ← Array.index_usize o.succ_z 10#usize
  let range5 ← Array.update range4 31#usize q13
  let q14 ← Array.index_usize o.xor12_z 10#usize
  let range6 ← Array.update range5 32#usize q14
  ok range6

def reconstruct (o : Openings) : K :=
  (R0P.valueReconstruct10 (fun i=>FIv_NativeArray.value o.z i.val)+
    R0P.valueReconstruct10 (fun i=>FIv_NativeArray.value o.succ_z i.val)*(1024 : K))+
    R0P.valueReconstruct10 (fun i=>FIv_NativeArray.value o.xor12_z i.val)*(1048576 : K)
def model (o : Openings) (old : Fin (33#usize).val → K) : Fin (33#usize).val → K :=
  Function.update (Function.update (Function.update old ⟨30,by decide⟩
    (FIv_NativeArray.value o.z 10-reconstruct o)) ⟨31,by decide⟩
    (FIv_NativeArray.value o.succ_z 10)) ⟨32,by decide⟩
    (FIv_NativeArray.value o.xor12_z 10)

theorem value (o : Openings) (range out : Array NQ 33#usize)
    (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z) (hr : canonical range)
    (success : run o range=ok out) : canonical out ∧ decoded out=model o (decoded range) := by
  unfold run at success
  obtain ⟨q5,h_q5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q6,h_q6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i,h_i,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q7,h_q7,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q8,h_q8,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q9,h_q9,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i1,h_i1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q10,h_q10,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨rec,h_rec,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q11,h_q11,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q12,h_q12,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range4,h_range4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q13,h_q13,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range5,h_range5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q14,h_q14,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range6,h_range6,success⟩ := FIv_Map.bind_success _ _ _ success
  have same : range6=out := Result.ok.inj success
  subst range6
  have v5 := FIx_ReconstructMeaning.value o.z q5 hz h_q5
  have v6 := FIx_ReconstructMeaning.value o.succ_z q6 hs h_q6
  have vi := FIy_ValueShifts.ten i h_i
  have v7 := FIw_ScalarArithmetic.mul q6 q7 i h_q7
  have v8 := FIv_NativeValue.add q5 q7 q8 v5.1 v7.1 h_q8
  have v9 := FIx_ReconstructMeaning.value o.xor12_z q9 hx h_q9
  have vi1 := FIy_ValueShifts.twenty i1 h_i1
  have v10 := FIw_ScalarArithmetic.mul q9 q10 i1 h_q10
  have vrec := FIv_NativeValue.add q8 q10 rec v8.1 v10.1 h_rec
  have c11 := FIv_NativeArray.canonical o.z 10#usize q11 hz h_q11
  have v12 := FIv_SubMap.qm q11 rec q12 c11 vrec.1 h_q12
  have u1 := FIw_ArrayValue.update range range4 30#usize q12 (by decide) hr v12.1 h_range4
  have c13 := FIv_NativeArray.canonical o.succ_z 10#usize q13 hs h_q13
  have u2 := FIw_ArrayValue.update range4 range5 31#usize q13 (by decide) u1.1 c13 h_range5
  have c14 := FIv_NativeArray.canonical o.xor12_z 10#usize q14 hx h_q14
  have u3 := FIw_ArrayValue.update range5 out 32#usize q14 (by decide) u2.1 c14 h_range6
  refine ⟨u3.1,?_⟩
  rw [u3.2,u2.2,u1.2,v12.2,vrec.2,v10.2,v8.2,v7.2,v5.2,v6.2,v9.2,vi,vi1,
    ←FIv_NativeArray.read o.z 10#usize q11 h_q11,
    ←FIv_NativeArray.read o.succ_z 10#usize q13 h_q13,
    ←FIv_NativeArray.read o.xor12_z 10#usize q14 h_q14]
  rfl
#print axioms value
end AspisR1.FIy_ValueTail
end
