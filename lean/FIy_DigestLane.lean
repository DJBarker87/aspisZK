import FIy_DigestTarget
import FIy_DigestArithmetic
import FIw_ArrayValue
import FIw_WordValue
import FIx_SelectedMeaning
import FIy_ArraySlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_DigestLane
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)

def run (lane : Usize) (output : Array NQ 8#usize) (selector : NQ)
    (opened : Array NQ 16#usize) (start : Usize) (expected : Array U32 8#usize) (right : Bool) :
    Result (Array NQ 8#usize) := do
  let target ← Array.index_usize expected lane
  let target1 ← FIy_DigestTarget.run lane target right
  let old ← Array.index_usize output lane
  let i ← start+lane
  let cell ← Array.index_usize opened i
  let updated ← FIy_DigestArithmetic.run old selector cell target1
  Array.update output lane updated

def target (expected : Array U32 8#usize) (right : Bool) (j : Nat) : Nat :=
  FIy_DigestTarget.value j ((expected.val[j]?).getD 0#u32) right

def increment (selector : NQ) (opened : Array NQ 16#usize) (start : Nat)
    (expected : Array U32 8#usize) (right : Bool) (j : Nat) : K :=
  decode selector*(FIv_NativeArray.value opened (start+j)-(target expected right j : K))

def model (lane : Nat) (selector : NQ) (opened : Array NQ 16#usize) (start : Nat)
    (expected : Array U32 8#usize) (right : Bool) (old : Fin (8#usize).val → K) : Fin (8#usize).val → K :=
  fun j=>if j.val=lane then old j+increment selector opened start expected right j.val else old j

theorem value (lane start : Usize) (output out : Array NQ 8#usize) (selector : NQ)
    (opened : Array NQ 16#usize) (expected : Array U32 8#usize) (right : Bool)
    (hl : lane.val<8) (hb : start.val+8≤16)
    (ho : canonical output) (hs : Canon selector) (ha : canonical opened)
    (he : ∀ x∈expected.val,x.val<FIw_ScalarArithmetic.P)
    (success : run lane output selector opened start expected right=ok out) :
    canonical out ∧ decoded out=model lane.val selector opened start.val expected right (decoded output) := by
  unfold run at success
  obtain ⟨t,ht,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨t1,ht1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨old,hold,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i,hi,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨cell,hcell,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨updated,hupdated,success⟩ := FIv_Map.bind_success _ _ _ success
  have targetSlot := FIy_ArraySlot.value expected lane t ht
  have tmem : t∈expected.val := List.mem_of_getElem? targetSlot
  have vt := FIy_DigestTarget.value_exact lane t t1 right hl (he t tmem) ht1
  have hcanon := vt.1
  have hvalue := vt.2
  have cold := FIv_NativeArray.canonical output lane old ho hold
  have ccell := FIv_NativeArray.canonical opened i cell ha hcell
  have vi := FIw_WordValue.add start lane i hi
  have vu := FIy_DigestArithmetic.value old selector cell updated t1 cold hs ccell hcanon hupdated
  have up := FIw_ArrayValue.update output out lane updated (by exact hl) ho vu.1 success
  have targetRead : (expected.val[lane.val]?).getD 0#u32=t := by rw [targetSlot];rfl
  refine ⟨up.1,?_⟩
  rw [up.2]
  funext j
  by_cases hj : j.val=lane.val
  · have eq : j=(⟨lane.val,by exact hl⟩ : Fin (8#usize).val) := Fin.ext hj
    rw [eq,Function.update_self]
    simp only [model,↓reduceIte]
    rw [vu.2,hvalue,←FIv_NativeArray.read output lane old hold,
      ←FIv_NativeArray.read opened i cell hcell,vi]
    simp only [increment,target,targetRead]
    rw [FIx_SelectedMeaning.read output lane.val (by exact hl)]
  · have ne : j≠(⟨lane.val,by exact hl⟩ : Fin (8#usize).val) := fun eq=>hj (congrArg Fin.val eq)
    rw [Function.update_of_ne ne]
    simp only [model,if_neg hj]
#print axioms value
end AspisR1.FIy_DigestLane
end
