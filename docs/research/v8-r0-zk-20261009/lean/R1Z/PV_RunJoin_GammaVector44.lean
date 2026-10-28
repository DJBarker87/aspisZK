import R1Z.PV_RunJoin_SourceArray44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaVector44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_BatchRowValue44 (table array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (c : Nat → Nat → Raw) (p : Nat → Raw)
    (hc : ∀ l, l < 29 → ∀ j, j < 1024 → canonical (c l j))
    (hp : ∀ l, l < 29 → canonical (p l)) :
    ∃ (z : Nat → Raw) (out : alloc.vec.Vec W),
      @prover.opening_batch_loop _ (ProverRwP6BodyCandidate.selected ops)
        (table c) (array 29#usize p) (alloc.vec.Vec.with_capacity W 1024#usize) 0#usize = .ok out ∧
      AspisR1ProducerRelease47.gamma53.all (ProverCommitGammaCell53.table c)
        (sourceArray 29#usize p) = .ok (sourceArray 1024#usize z) ∧
      Array.to_slice (array 1024#usize z) = alloc.vec.Vec.deref out ∧
      (∀ j, j < 1024 → canonical (z j)) ∧
      ∀ j : Fin 1024, value (z j.val) = sum (fun l => c l j.val) p 29 0 := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitGammaOutput53.all c hc p hp
  obtain ⟨out,hout,hv⟩ := PV_RunJoin_BatchLoopValue44.complete ops c p z hc hp hcz
    (fun j hj => hdz ⟨j,hj⟩) 1024 (alloc.vec.Vec.with_capacity W 1024#usize) 0#usize
    (by rfl) (by have := ProverCommitPairCounter47.usize_large;change 0+1024 ≤ Usize.max;omega)
  refine ⟨z,out,?_,hz,?_,hcz,hdz⟩
  · rw [@PV_RunJoin_BatchThread44.complete _ (ProverRwP6BodyCandidate.selected ops)
      (table c) (array 29#usize p) _ 0#usize 1024 (by rfl)]
    exact hout
  · apply Subtype.ext
    change (array 1024#usize z).val = out.val
    rw [hv,PV_RunJoin_SourceArray44.payload]
    simp only [alloc.vec.Vec.with_capacity,List.nil_append,Nat.zero_add,array,ProverCommitArray49.array]
#print axioms complete
end R1Z.PV_RunJoin_GammaVector44
