import Aeneas
import ExtractedCurrentReducerOps
import Lean.Elab.Tactic.Omega

/- Literal emitted row driver with explicit backend parameters. Backend laws
are not axioms and no concrete backend or production-caller join is assumed. -/
set_option autoImplicit false
namespace S7Kani2AccumulatorLoop
open Aeneas Aeneas.Std Result
structure K where
  c0 : U32 × U32
  c1 : U32 × U32
structure E where
  c0 : K
  c1 : K
structure BatchedWeights where
  raw : alloc.vec.Vec (Array U64 4#usize)
  terms : Usize
structure Backend where
  push : BatchedWeights → Usize → K → U32 → Result BatchedWeights
  from_qm31 : K → Result E
  from_m31 : U32 → Result E
  trace : U16 → Usize → E → Result Unit
abbrev State := alloc.vec.Vec K × BatchedWeights

def step (backend : Backend) (basis : Array U32 256#usize)
    (power : K) (next width j : Usize) (state : State) : Result State := do
  let m ← Array.index_usize basis j
  let weights1 ← backend.push state.2 j power m
  let i ← next * width
  let i1 ← i + j
  let q ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      K) state.1 j
  let we ← backend.from_qm31 q
  backend.trace 12#u16 i1 we
  let i2 ← i + j
  let we1 ←
    backend.from_m31
      m
  backend.trace 13#u16 i2 we1
  ok (state.1, weights1)

def accumulate_rows_owned (backend : Backend)
  (output_weights : alloc.vec.Vec K)
  (weights : BatchedWeights) (basis : Array U32 256#usize)
  (power : K) (next : Std.Usize) (width : Std.Usize)
  (j : Std.Usize) :
  Result ((alloc.vec.Vec K) × BatchedWeights)
  := do
  if j >= width
  then ok (output_weights, weights)
  else
    let m ← Array.index_usize basis j
    let weights1 ← backend.push weights j power m
    let i ← next * width
    let i1 ← i + j
    let q ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        K) output_weights j
    let we ← backend.from_qm31 q
    backend.trace 12#u16 i1 we
    let i2 ← i + j
    let we1 ←
      backend.from_m31
        m
    backend.trace 13#u16 i2 we1
    let i3 ← j + 1#usize
    accumulate_rows_owned backend output_weights weights1 basis power next width i3
partial_fixpoint

def iterate (f : Usize → State → Result State) : Nat → Usize → State → Result State
 | 0, _, state => ok state
 | n+1, j, state => do
     let state1 ← f j state
     let j1 ← j + 1#usize
     iterate f n j1 state1

/-- The checked increment is total on every nonterminal production row. -/
theorem increment (j : Usize) (h : j.val < 256) :
    ∃ j1, (j + 1#usize : Result Usize) = ok j1 ∧ j1.val = j.val+1 := by
  apply AspisR1.ExtractedCurrentReducerOps.tryMk_success
  have hb : 256 < 2^UScalarTy.Usize.numBits := by scalar_tac
  change j.val + 1 < 2^UScalarTy.Usize.numBits
  omega

/-- Actual emitted recurrence equals bounded composition, retaining checked
errors and divergence from each backend step. No step-success premise. -/
theorem extracted_loop_composition (backend : Backend)
    (basis : Array U32 256#usize) (power : K) (next width j : Usize)
    (n : Nat) (state : State) (hwidth : width.val ≤ 256)
    (remaining : j.val+n=width.val) :
    accumulate_rows_owned backend state.1 state.2 basis power next width j =
      iterate (step backend basis power next width) n j state := by
  induction n generalizing j state with
  | zero =>
      have stop : j ≥ width := by scalar_tac
      rw [accumulate_rows_owned]
      simp only [stop, if_pos, iterate]
  | succ n ih =>
      rcases state with ⟨output_weights, weights⟩
      have running : ¬ j ≥ width := by scalar_tac
      obtain ⟨j1, hj1, hv⟩ := increment j (by omega)
      rw [accumulate_rows_owned]
      simp only [running, if_false, iterate, step, bind_tc_ok, bind_assoc_eq]
      simp only [bind_assoc_eq, bind_tc_ok]
      congr 1
      funext m
      congr 1
      funext weights1
      congr 1
      funext i
      congr 1
      funext i1
      congr 1
      funext q
      congr 1
      funext we
      congr 1
      funext unit1
      congr 1
      funext i2
      congr 1
      funext we1
      congr 1
      funext unit2
      simp only [hj1, bind_tc_ok]
      exact ih j1 (output_weights,weights1) (by omega)

#print axioms increment
#print axioms extracted_loop_composition
end S7Kani2AccumulatorLoop
