import R1Z.PV_RunJoin_FibreFillThread43
import R1Z.PV_RunJoin_OpeningLane43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FibreOpening43
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Matrix := Array (Array W 29#usize) 4#usize

def step (ops : ExternalFuns) (c : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex)
    (values : Matrix) (j : Usize) : Result Matrix := do
  let lane ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.Usize)
      c.lanes j
  let w ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      host_commitment.Word) c.words j
  let row ← @PV_RunJoin_OpeningLane43.row _ (ProverRwP6BodyCandidate.selected ops) ops w u
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

def phase (ops : ExternalFuns) : Nat → host_commitment.Commitment →
    aspis_core.r0.domain.FibreIndex → Matrix → Usize → Result Matrix
  | 0, _, _, values, _ => .ok values
  | n+1, c, u, values, j => do
    let next ← step ops c u values j
    phase ops n c u next (Usize.wrapping_add j 1#usize)

theorem step_exact (ops : ExternalFuns) (c : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (values : Matrix) (j : Usize) :
    @PV_RunJoin_FibreFillThread43.step _ (ProverRwP6BodyCandidate.selected ops) c u values j=
      step ops c u values j := by
  unfold PV_RunJoin_FibreFillThread43.step step
  simp only [PV_RunJoin_OpeningLane43.complete]

theorem phase_exact (ops : ExternalFuns) (n : Nat) (c : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (values : Matrix) (j : Usize) :
    @PV_RunJoin_FibreFillThread43.phase _ (ProverRwP6BodyCandidate.selected ops) n c u values j=
      phase ops n c u values j := by
  induction n generalizing values j with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_FibreFillThread43.phase,phase,step_exact]
    apply congrArg (Aeneas.Std.bind (step ops c u values j))
    funext next
    exact ih next (Usize.wrapping_add j 1#usize)

theorem values_complete (ops : ExternalFuns) (n : Nat) (c : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (values : Matrix) (j : Usize)
    (bound : j.val+n=c.lanes.length) (small : c.lanes.length≤29) :
    @host_commitment.fill_opening_values _ (ProverRwP6BodyCandidate.selected ops) c u values j=
      phase ops n c u values j := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  rw [PV_RunJoin_FibreFillThread43.thread n c u values j bound small,phase_exact]

/-- The actual constructor is the ordered finite stored-word fill, followed
by the exact path-slot update. No successful helper Result is a premise. -/
def run (ops : ExternalFuns) (c : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) :
    Result aspis_core.r0.wire.FibreOpening := do
  let values ← phase ops c.lanes.length c u out.values 0#usize
  let path ← @host_commitment.opening_path _ (ProverRwP6BodyCandidate.selected ops) c.time
  let zero := Array.repeat 32#usize 0#u8
  let paths ← Array.update out.paths path (Array.repeat 6#usize (Array.repeat 7#usize zero))
  .ok { values, paths }

theorem complete (ops : ExternalFuns) (c : host_commitment.Commitment)
    (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening)
    (small : c.lanes.length≤29) :
    @host_commitment.Commitment.fill_opening _ (ProverRwP6BodyCandidate.selected ops) c u out=
      run ops c u out := by
  unfold host_commitment.Commitment.fill_opening run
  rw [values_complete ops c.lanes.length c u out.values 0#usize (by change 0+c.lanes.length=c.lanes.length;omega) small]
#print axioms step_exact
#print axioms phase_exact
#print axioms values_complete
#print axioms complete
end R1Z.PV_RunJoin_FibreOpening43
