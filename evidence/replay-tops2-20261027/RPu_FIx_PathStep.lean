import RPu_FIx_PathIndices
import RPu_FIw_ArrayReadValue
import RPu_FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PathStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)

def run (lane : Usize) (selector : NQ) (a a1 : Array NQ 16#usize) (bit : NQ)
    (path : Array NQ 17#usize) : Result (Array NQ 17#usize) := do
  let i ← 1#usize+lane
  let current ← Array.index_usize a i
  let q ← field.QM31.sub field.QM31.ONE bit
  let q1 ← field.QM31.mul selector q
  let q2 ← Array.index_usize a1 lane
  let q3 ← field.QM31.sub q2 current
  let q4 ← field.QM31.mul q1 q3
  let path1 ← Array.update path i q4
  let q5 ← field.QM31.mul selector bit
  let i1 ← poseidon2.RATE+lane
  let q6 ← Array.index_usize a1 i1
  let q7 ← field.QM31.sub q6 current
  let q8 ← field.QM31.mul q5 q7
  let i2 ← 1#usize+poseidon2.DIGEST_ELEMS
  let i3 ← i2+lane
  Array.update path1 i3 q8

def model (lane : Usize) (hl : lane.val<8) (selector bit : NQ) (a a1 : Array NQ 16#usize)
    (old : Fin (17#usize).val → K) : Fin (17#usize).val → K :=
  Function.update (Function.update old ⟨1+lane.val,by change 1+lane.val<17;omega⟩
    (decode selector*(1-decode bit)*(FIv_NativeArray.value a1 lane.val-FIv_NativeArray.value a (1+lane.val))))
    ⟨9+lane.val,by change 9+lane.val<17;omega⟩
    (decode selector*decode bit*(FIv_NativeArray.value a1 (8+lane.val)-FIv_NativeArray.value a (1+lane.val)))

theorem value (lane : Usize) (selector bit : NQ) (a a1 : Array NQ 16#usize)
    (path out : Array NQ 17#usize) (hl : lane.val<8)
    (hs : Canon selector) (hb : Canon bit) (ha : canonical a) (ha1 : canonical a1) (hp : canonical path)
    (success : run lane selector a a1 bit path=ok out) :
    canonical out ∧ decoded out=model lane hl selector bit a a1 (decoded path) := by
  unfold run at success
  obtain ⟨i,hi,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨current,hcurrent,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q,hq,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,hq1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,hq2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q3,hq3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q4,hq4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨path1,hpath1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q5,hq5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i1,hi1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q6,hq6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q7,hq7,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q8,hq8,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i2,hi2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i3,hi3,success⟩ := FIv_Map.bind_success _ _ _ success
  have vi := FIx_PathIndices.first lane i hi
  have vi1 := FIx_PathIndices.rate lane i1 hi1
  have vi2 := FIx_PathIndices.digest i2 hi2
  have vi3 := FIx_PathIndices.final lane i2 i3 vi2 hi3
  have vc := FIv_NativeArray.canonical a i current ha hcurrent
  have vq := FIv_SubMap.qm field.QM31.ONE bit q FIv_NativeValue.one.1 hb hq
  have vq1 := FIv_NativeValue.mul selector q q1 hs vq.1 hq1
  have vq2 := FIv_NativeArray.canonical a1 lane q2 ha1 hq2
  have vq3 := FIv_SubMap.qm q2 current q3 vq2 vc hq3
  have vq4 := FIv_NativeValue.mul q1 q3 q4 vq1.1 vq3.1 hq4
  have update1 := FIw_ArrayValue.update path path1 i q4 (FIx_PathIndices.first_bound lane i hl vi) hp vq4.1 hpath1
  have vq5 := FIv_NativeValue.mul selector bit q5 hs hb hq5
  have vq6 := FIv_NativeArray.canonical a1 i1 q6 ha1 hq6
  have vq7 := FIv_SubMap.qm q6 current q7 vq6 vc hq7
  have vq8 := FIv_NativeValue.mul q5 q7 q8 vq5.1 vq7.1 hq8
  have update2 := FIw_ArrayValue.update path1 out i3 q8 (FIx_PathIndices.last_bound lane i3 hl vi3) update1.1 vq8.1 success
  refine ⟨update2.1,?_⟩
  rw [update2.2,update1.2,vq8.2,vq7.2,vq5.2,vq4.2,vq3.2,vq1.2,vq.2,FIv_NativeValue.one.2,
    ←FIv_NativeArray.read a1 i1 q6 hq6,←FIv_NativeArray.read a1 lane q2 hq2,
    ←FIv_NativeArray.read a i current hcurrent]
  simp only [vi,vi1,vi3,model]

#print axioms value
end AspisR1.FIx_PathStep
end
