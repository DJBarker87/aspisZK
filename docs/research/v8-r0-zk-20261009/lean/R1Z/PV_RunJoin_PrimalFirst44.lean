import R1Z.PV_RunJoin_FoldCallerValue44
import R1Z.ProverCommitFoldOutput48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrimalFirst44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (q : Nat → Raw) (hq : ∀ j, j < 1024 → canonical (q j))
    (a : Raw) (ha : canonical a) :
    ∃ (z : Nat → Raw) (out : alloc.vec.Vec W),
      @prover.fold _ (ProverRwP6BodyCandidate.selected ops) (Array.to_slice (array 1024#usize q))
        (current (source a)) false = .ok out ∧
      AspisR1ProducerRelease47.fold_first (sourceArray 1024#usize q) (source a)
        (Array.repeat 256#usize AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) 0#usize 256#u16 =
        .ok (sourceArray 256#usize z) ∧
      Array.to_slice (array 256#usize z) = alloc.vec.Vec.deref out ∧
      (∀ j, j < 256 → canonical (z j)) ∧
      ∀ j, j < 256 → value (z j) = ProverCommitFoldOutput48.mathCell (fun i => value (q i)) (value a) j := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitFoldOutput48.first_exact q hq a ha
  obtain ⟨out,hout,himage⟩ := PV_RunJoin_FoldCallerValue44.complete ops 1024#usize 256#usize rfl (by decide)
    q z a false hq ha hcz (fun j hj => by
      simpa only [ProverCommitFoldOutput48.mathCell,PV_RunJoin_FoldStepValue44.model,
        Bool.false_eq_true,↓reduceIte,PV_RunJoin_FoldCell44.polynomial,Nat.add_zero] using hdz j hj)
  exact ⟨z,out,hout,hz,himage,hcz,hdz⟩
#print axioms complete
end R1Z.PV_RunJoin_PrimalFirst44
