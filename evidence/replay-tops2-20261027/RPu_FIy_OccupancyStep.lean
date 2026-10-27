import RPu_FIx_PathLoop
import RPu_FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)

def run (lane : Usize) (opened : Array NQ 16#usize) (oneMinus both : NQ)
    (occupancy : Array NQ 12#usize) : Result (Array NQ 12#usize) := do
  let i ← 2#usize+lane
  let q ← Array.index_usize opened i
  let q1 ← field.QM31.mul oneMinus q
  let q2 ← field.QM31.mul both q1
  let i1 ← 3#usize+lane
  Array.update occupancy i1 q2

def model (lane : Nat) (opened : Array NQ 16#usize) (oneMinus both : NQ)
    (old : Fin (12#usize).val → K) : Fin (12#usize).val → K := fun j=>
  if j.val=3+lane then decode both*(decode oneMinus*FIv_NativeArray.value opened (2+lane)) else old j

theorem value (lane : Usize) (opened : Array NQ 16#usize) (oneMinus both : NQ)
    (occupancy out : Array NQ 12#usize) (hl : lane.val<8)
    (ha : canonical opened) (hm : Canon oneMinus) (hb : Canon both) (hc : canonical occupancy)
    (success : run lane opened oneMinus both occupancy=ok out) :
    canonical out ∧ decoded out=model lane.val opened oneMinus both (decoded occupancy) := by
  unfold run at success
  obtain ⟨i,hi,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q,hq,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,hq1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,hq2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i1,hi1,success⟩ := FIv_Map.bind_success _ _ _ success
  have vi := FIw_WordValue.add 2#usize lane i hi
  have vi1 := FIw_WordValue.add 3#usize lane i1 hi1
  have c := FIv_NativeArray.canonical opened i q ha hq
  have m1 := FIv_NativeValue.mul oneMinus q q1 hm c hq1
  have m2 := FIv_NativeValue.mul both q1 q2 hb m1.1 hq2
  have hu := FIw_ArrayValue.update occupancy out i1 q2 (by change i1.val<12;change i1.val=3+lane.val at vi1;omega) hc m2.1 success
  refine ⟨hu.1,?_⟩
  rw [hu.2,m2.2,m1.2,←FIv_NativeArray.read opened i q hq]
  funext j
  change i.val=2+lane.val at vi
  change i1.val=3+lane.val at vi1
  by_cases he : j.val=3+lane.val
  · have hj : j=(⟨i1.val,by change i1.val<12;omega⟩ : Fin (12#usize).val) := Fin.ext (he.trans vi1.symm)
    rw [hj,Function.update_self]
    simp [model,vi1,vi]
  · have hj : j≠(⟨i1.val,by change i1.val<12;omega⟩ : Fin (12#usize).val) := by
      intro eq
      apply he
      exact (congrArg Fin.val eq).trans vi1
    rw [Function.update_of_ne hj]
    simp only [model,if_neg he]
#print axioms value
end AspisR1.FIy_OccupancyStep
end
