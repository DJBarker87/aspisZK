import RPv_FJa_PoseidonPow5
import RPv_FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_QmRoundStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev State := Array NQ 16#usize
def step (a state : State) (lane : Usize) : Result State := do
  let x ← Array.index_usize state lane
  let y ← Array.index_usize a lane
  let z ← field.QM31.add x y
  let z5 ← state_only_poseidon.pow5 z
  Array.update state lane z5
/-- The actual add/update cell; neither output nor canonicality is supplied. -/
theorem value (a state out : State) (lane : Usize) (hl : lane.val<16)
    (ha : canonical a) (hs : canonical state) (run : step a state lane=ok out) :
    canonical out ∧ decoded out=Function.update (decoded state) ⟨lane.val,hl⟩
      ((decoded state ⟨lane.val,hl⟩+decoded a ⟨lane.val,hl⟩)^5) := by
  unfold step at run
  obtain ⟨x,hx,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨z,hz,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨z5,hz5,run⟩ := FIv_Map.bind_success _ _ _ run
  have vx := FIw_ArrayReadValue.read state lane hl x hx
  have vy := FIw_ArrayReadValue.read a lane hl y hy
  have vz := FIv_NativeValue.add x y z
    (FIv_NativeArray.canonical state lane x hs hx)
    (FIv_NativeArray.canonical a lane y ha hy) hz
  have v5 := FJa_PoseidonPow5.value z z5 vz.1 hz5
  have vout := FIw_ArrayValue.update state out lane z5 hl hs v5.1 run
  refine ⟨vout.1,?_⟩
  rw [vout.2,v5.2,vz.2,vx,vy]
/-- Both installed nonlinear traversals have the same per-cell body. -/
def loop (packed : Bool) (iter : core.ops.range.Range Usize) (a state : State) : Result State :=
  if packed then state_only_poseidon.full_round_packed_loop iter state a
  else state_only_poseidon.full_round_loop iter state a

theorem unfold_loop (packed : Bool) (iter : core.ops.range.Range Usize) (a state : State) :
    loop packed iter a state = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok state
      | some lane =>
        let next ← step a state lane
        loop packed iter1 a next) := by
  cases packed with
  | false =>
    simp only [loop,Bool.false_eq_true,↓reduceIte]
    rw [state_only_poseidon.full_round_loop.eq_def]
    simp only [step,bind_assoc_eq]
    rfl
  | true =>
    simp only [loop,↓reduceIte]
    rw [state_only_poseidon.full_round_packed_loop.eq_def]
    simp only [step,bind_assoc_eq]
    rfl
#print axioms value
#print axioms unfold_loop
end AspisR1.FJb_QmRoundStep
end
