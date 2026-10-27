import RPv_FJa_PoseidonPow5
import RPv_FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_LeadingStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev State := Array NQ 16#usize
def step (a state : State) (lane : Usize) : Result State := do
  let x ← Array.index_usize state lane
  let y ← Array.index_usize a lane
  let z ← field.QM31.add x y
  Array.update state lane z
/-- The actual add/update cell; neither output nor canonicality is supplied. -/
theorem value (a state out : State) (lane : Usize) (hl : lane.val<16)
    (ha : canonical a) (hs : canonical state) (run : step a state lane=ok out) :
    canonical out ∧ decoded out=Function.update (decoded state) ⟨lane.val,hl⟩
      (decoded state ⟨lane.val,hl⟩+decoded a ⟨lane.val,hl⟩) := by
  unfold step at run
  obtain ⟨x,hx,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨y,hy,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨z,hz,run⟩ := FIv_Map.bind_success _ _ _ run
  have vx := FIw_ArrayReadValue.read state lane hl x hx
  have vy := FIw_ArrayReadValue.read a lane hl y hy
  have vz := FIv_NativeValue.add x y z
    (FIv_NativeArray.canonical state lane x hs hx)
    (FIv_NativeArray.canonical a lane y ha hy) hz
  have vout := FIw_ArrayValue.update state out lane z hl hs vz.1 run
  refine ⟨vout.1,?_⟩
  rw [vout.2,vz.2,vx,vy]
/-- One symbolic unfolding of the installed loop, independent of its span. -/
theorem unfold_loop (iter : core.ops.range.Range Usize) (a state : State) :
    state_only_poseidon.leading_pair_packed_loop iter a state = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok state
      | some lane =>
        let next ← step a state lane
        state_only_poseidon.leading_pair_packed_loop iter1 a next) := by
  rw [state_only_poseidon.leading_pair_packed_loop.eq_def]
  simp only [step,bind_assoc_eq]
  rfl
#print axioms value
#print axioms unfold_loop
end AspisR1.FJb_LeadingStep
end
