import R1Z.PV_RunJoin_BackendMatrix58
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendWrite58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_BackendMatrix58

theorem index_mut (p : Nat → Nat → W) (lane : Usize) (hl : lane.val<29) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Column) (matrix p) lane=
      ok (ProverCommitArray49.array 1024#usize (p lane.val),alloc.vec.Vec.set (matrix p) lane) := by
  obtain ⟨⟨a,back⟩,hr,hv,hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec (matrix p) lane (by rw [length];exact hl))
  have ha : a=ProverCommitArray49.array 1024#usize (p lane.val) := by
    simpa only [matrix,List.getElem_ofFn] using hv
  rw [alloc.vec.Vec.index_mut_slice_index,hr,ha,hback]

def write (self : prover.Backend) (lane row : Usize) (value : W) : Result prover.Backend := do
  let (a,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Column) self.messages lane
  let next ← Array.update a row value
  ok {self with messages:=back next}

theorem complete [ExternalTypes] (self : prover.Backend) (p : Nat → Nat → W)
    (hp : self.messages=matrix p) (lane row : Usize) (hl : lane.val<29) (hr : row.val<1024) (v : W) :
    write self lane row v=ok {self with messages:=matrix
      (Function.update p lane.val (Function.update (p lane.val) row.val v))} := by
  unfold write
  rw [hp,index_mut p lane hl]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  rw [ProverCommitArray49.update _ _ row hr]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_BackendMatrix58.set p lane hl]

#print axioms index_mut
#print axioms complete
end R1Z.PV_RunJoin_BackendWrite58
