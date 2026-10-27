import RPv_FIy_OccupancyStep
import RPv_FIw_ScalarArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyTail
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)

def run (input output : NQ) (expected : U32) (opened : Array NQ 16#usize)
    (occupied oneMinus : NQ) (occupancy : Array NQ 12#usize) : Result (Array NQ 12#usize) := do
  let q9 ← Array.index_usize opened 10#usize
  let q10 ← field.QM31.mul q9 oneMinus
  let q11 ← field.QM31.mul input q10
  let q12 ← pool_v1.pair_forest_semantic_terminal.lift_m31 expected
  let q13 ← field.QM31.sub occupied q12
  let q14 ← field.QM31.mul output q13
  let q15 ← field.QM31.add q11 q14
  Array.update occupancy 11#usize q15

def scalar (input output occupied oneMinus : K) (expected : Nat) (opened : Nat → K) : K :=
  input*(opened 10*oneMinus)+output*(occupied-(expected : K))

theorem value (input output occupied oneMinus : NQ) (expected : U32)
    (opened : Array NQ 16#usize) (occupancy out : Array NQ 12#usize)
    (hi : Canon input) (ho : Canon output) (hc : Canon occupied) (hm : Canon oneMinus)
    (he : expected.val<FIw_ScalarArithmetic.P) (ha : canonical opened) (hp : canonical occupancy)
    (success : run input output expected opened occupied oneMinus occupancy=ok out) :
    canonical out ∧ decoded out=Function.update (decoded occupancy) ⟨11,by decide⟩
      (scalar (decode input) (decode output) (decode occupied) (decode oneMinus)
        expected.val (FIv_NativeArray.value opened)) := by
  unfold run at success
  obtain ⟨q9,h9,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q10,h10,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q11,h11,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q12,h12,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q13,h13,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q14,h14,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q15,h15,success⟩ := FIv_Map.bind_success _ _ _ success
  have c9 := FIv_NativeArray.canonical opened 10#usize q9 ha h9
  have v10 := FIv_NativeValue.mul q9 oneMinus q10 c9 hm h10
  have v11 := FIv_NativeValue.mul input q10 q11 hi v10.1 h11
  have same := Result.ok.inj ((FIw_ScalarArithmetic.lift_run expected).symm.trans h12)
  have v12 := FIw_ScalarArithmetic.lift_value expected he
  rw [same] at v12
  have v13 := FIv_SubMap.qm occupied q12 q13 hc v12.1 h13
  have v14 := FIv_NativeValue.mul output q13 q14 ho v13.1 h14
  have v15 := FIv_NativeValue.add q11 q14 q15 v11.1 v14.1 h15
  have update := FIw_ArrayValue.update occupancy out 11#usize q15 (by decide) hp v15.1 success
  refine ⟨update.1,?_⟩
  rw [update.2,v15.2,v14.2,v13.2,v12.2,v11.2,v10.2,
    ←FIv_NativeArray.read opened 10#usize q9 h9]
  rfl
#print axioms value
end AspisR1.FIy_OccupancyTail
end
