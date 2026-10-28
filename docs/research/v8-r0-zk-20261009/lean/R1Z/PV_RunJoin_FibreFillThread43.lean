import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FibreFillThread43
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Matrix := Array (Array W 29#usize) 4#usize

/-- One actual stored commitment lane, with all four borrow restorations. -/
def step (c : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex)
    (values : Matrix) (j : Usize) : Result Matrix := do
  let lane ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize)
      c.lanes j
  let w ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      host_commitment.Word) c.words j
  let row ← host_commitment.opening_lane_values w u
  let we ← Array.index_usize row 0#usize
  let (a, index_mut_back) ← Array.index_mut_usize values 0#usize
  let a1 ← Array.update a lane we
  let we1 ← Array.index_usize row 1#usize
  let values1 := index_mut_back a1
  let (a2, index_mut_back1) ← Array.index_mut_usize values1 1#usize
  let a3 ← Array.update a2 lane we1
  let we2 ← Array.index_usize row 2#usize
  let values2 := index_mut_back1 a3
  let (a4, index_mut_back2) ← Array.index_mut_usize values2 2#usize
  let a5 ← Array.update a4 lane we2
  let we3 ← Array.index_usize row 3#usize
  let values3 := index_mut_back2 a5
  let (a6, index_mut_back3) ← Array.index_mut_usize values3 3#usize
  let a7 ← Array.update a6 lane we3
  let values4 := index_mut_back3 a7
  ok values4

def phase : Nat → host_commitment.Commitment → aspis_core.r0.domain.FibreIndex →
    Matrix → Usize → Result Matrix
  | 0, _, _, values, _ => .ok values
  | n+1, c, u, values, j => do
    let next ← step c u values j
    phase n c u next (Usize.wrapping_add j 1#usize)

theorem one_step (c : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex)
    (values : Matrix) (j : Usize) (more : j≠alloc.vec.Vec.len c.lanes) :
    host_commitment.fill_opening_values c u values j=(do
      let next ← step c u values j
      host_commitment.fill_opening_values c u next (Usize.wrapping_add j 1#usize)) := by
  rw [host_commitment.fill_opening_values]
  simp only [more,↓reduceIte,step,Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok,lift]

theorem thread (n : Nat) (c : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (values : Matrix) (j : Usize)
    (bound : j.val+n=c.lanes.length) (small : c.lanes.length≤29) :
    host_commitment.fill_opening_values c u values j=phase n c u values j := by
  induction n generalizing j values with
  | zero =>
    have stop : j=alloc.vec.Vec.len c.lanes := by
      apply UScalar.eq_of_val_eq
      change j.val=c.lanes.length
      omega
    rw [host_commitment.fill_opening_values]
    simp only [stop,↓reduceIte,phase]
  | succ n ih =>
    have more : j≠alloc.vec.Vec.len c.lanes := by
      intro h
      have hv := congrArg UScalar.val h
      change j.val=c.lanes.length at hv
      omega
    rw [one_step c u values j more,phase]
    apply congrArg (Aeneas.Std.bind (step c u values j))
    funext next
    have inc := PV_RunJoin_MergeLoop35.increment j (by omega)
    exact ih next (Usize.wrapping_add j 1#usize) (by rw [inc];omega)
#print axioms one_step
#print axioms thread
end R1Z.PV_RunJoin_FibreFillThread43
