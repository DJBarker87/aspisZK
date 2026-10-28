import R1Z.PV_RunJoin_FoldCallerValue44
import R1Z.ProverCommitDualOutput49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DualFirst44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (q : Nat → Raw) (hq : ∀ j, j < 1024 → canonical (q j))
    (a : Raw) (ha : canonical a) :
    ∃ (z : Nat → Raw) (out : alloc.vec.Vec W),
      @prover.fold _ (ProverRwP6BodyCandidate.selected ops) (Array.to_slice (array 1024#usize q))
        (current (source a)) true = .ok out ∧
      AspisR1ProducerRelease47.dual.all (sourceArray 1024#usize q) (source a) = .ok (sourceArray 256#usize z) ∧
      Array.to_slice (array 256#usize z) = alloc.vec.Vec.deref out ∧
      (∀ j, j < 256 → canonical (z j)) ∧
      ∀ j : Fin 256, value (z j.val) = AspisR1.RoundPairing.dualFold (value a)
        (fun i : Fin 1024 => value (q i.val)) j := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitDualOutput49.all q hq a ha
  obtain ⟨out,hout,himage⟩ := PV_RunJoin_FoldCallerValue44.complete ops 1024#usize 256#usize rfl (by decide)
    q z a true hq ha hcz (fun j hj => by
      have hv := hdz ⟨j,hj⟩
      rw [← ProverCommitDualOutput49.cell_model q (value a) ⟨j,hj⟩] at hv
      simpa only [PV_RunJoin_FoldStepValue44.model,↓reduceIte,
        PV_RunJoin_DualCell44.polynomial,ProverCommitDualFill49.cellValue,
        ProverCommitDualCell48.polynomial] using hv)
  exact ⟨z,out,hout,hz,himage,hcz,hdz⟩
#print axioms complete
end R1Z.PV_RunJoin_DualFirst44
