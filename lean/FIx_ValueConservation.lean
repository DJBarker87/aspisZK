import FIv_SubMap
import FIv_NativeArray
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ValueConservation
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)

def run (selector : NQ) (z succ : Array NQ 16#usize) : Result (Array NQ 2#usize) := do
  let q0 ← Array.index_usize z 0#usize
  let q1 ← Array.index_usize z 1#usize
  let d0 ← field.QM31.sub q0 q1
  let q2 ← Array.index_usize z 2#usize
  let d1 ← field.QM31.sub d0 q2
  let a ← field.QM31.mul selector d1
  let q3 ← Array.index_usize succ 0#usize
  let q4 ← Array.index_usize succ 1#usize
  let d2 ← field.QM31.sub q3 q4
  let b ← field.QM31.mul selector d2
  ok (Array.make 2#usize [a,b])

def model (selector : K) (z succ : Nat → K) : List K :=
  [selector*((z 0-z 1)-z 2),selector*(succ 0-succ 1)]

theorem value (selector : NQ) (z succ : Array NQ 16#usize) (out : Array NQ 2#usize)
    (hs : Canon selector) (hz : FIw_ArrayValue.canonical z) (ht : FIw_ArrayValue.canonical succ)
    (success : run selector z succ=ok out) :
    FIw_ArrayValue.canonical out ∧ out.val.map decode=model (decode selector)
      (FIv_NativeArray.value z) (FIv_NativeArray.value succ) := by
  unfold run at success
  obtain ⟨q0,h0,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,h1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d0,hd0,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,h2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d1,hd1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨a,ha,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q3,h3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q4,h4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d2,hd2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨b,hb,success⟩ := FIv_Map.bind_success _ _ _ success
  cases Result.ok.inj success
  have c0 := FIv_NativeArray.canonical z 0#usize q0 hz h0
  have c1 := FIv_NativeArray.canonical z 1#usize q1 hz h1
  have c2 := FIv_NativeArray.canonical z 2#usize q2 hz h2
  have c3 := FIv_NativeArray.canonical succ 0#usize q3 ht h3
  have c4 := FIv_NativeArray.canonical succ 1#usize q4 ht h4
  have v0 := FIv_SubMap.qm q0 q1 d0 c0 c1 hd0
  have v1 := FIv_SubMap.qm d0 q2 d1 v0.1 c2 hd1
  have va := FIv_NativeValue.mul selector d1 a hs v1.1 ha
  have v2 := FIv_SubMap.qm q3 q4 d2 c3 c4 hd2
  have vb := FIv_NativeValue.mul selector d2 b hs v2.1 hb
  constructor
  · intro x hx
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact va.1
    · exact vb.1
  · simp only [Array.make,List.map_cons,List.map_nil,model,va.2,vb.2,v0.2,v1.2,v2.2,
      ←FIv_NativeArray.read z 0#usize q0 h0,←FIv_NativeArray.read z 1#usize q1 h1,
      ←FIv_NativeArray.read z 2#usize q2 h2,←FIv_NativeArray.read succ 0#usize q3 h3,
      ←FIv_NativeArray.read succ 1#usize q4 h4]
    rfl
#print axioms value
end AspisR1.FIx_ValueConservation
end
