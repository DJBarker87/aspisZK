import R1Z.PV_RunJoin_RoundSecond44
import R1Z.PV_RunJoin_PrimalFirst44
import R1Z.PV_RunJoin_PrimalSecond44
import R1Z.PV_RunJoin_DualFirst44
import R1Z.ProverCommitOpeningKernel49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningKernel44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

/-- Actual current round/fold calls in producer order, with the transcript
separately supplying the two retained challenges. This is a source arithmetic
kernel; its binding to prepare_opening/finish_opening remains separate. -/
def run (ops : ExternalFuns) (q w : Slice W) (a b : W) := do
  let c0 ← @prover.round _ (ProverRwP6BodyCandidate.selected ops) q w
  let q1 ← @prover.fold _ (ProverRwP6BodyCandidate.selected ops) q a false
  let w1 ← @prover.fold _ (ProverRwP6BodyCandidate.selected ops) w a true
  let c1 ← @prover.round _ (ProverRwP6BodyCandidate.selected ops) (alloc.vec.Vec.deref q1) (alloc.vec.Vec.deref w1)
  let fin ← @prover.fold _ (ProverRwP6BodyCandidate.selected ops) (alloc.vec.Vec.deref q1) b false
  .ok (c0,q1,c1,fin)

theorem complete (ops : ExternalFuns) (q w : Nat → Raw)
    (hq : ∀ j, j < 1024 → canonical (q j)) (hw : ∀ j, j < 1024 → canonical (w j))
    (a b : Raw) (ha : canonical a) (hb : canonical b) :
    ∃ (c0 q1 c1 fin : Nat → Raw) (vq : alloc.vec.Vec W) (vf : alloc.vec.Vec W),
      run ops (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))
        (current (source a)) (current (source b)) = .ok (array 7#usize c0,vq,array 7#usize c1,vf) ∧
      ProverCommitOpeningKernel49.run (sourceArray 1024#usize q) (sourceArray 1024#usize w) (source a) (source b) =
        .ok (List.ofFn (fun k : Fin 7 => source (c0 k.val)),sourceArray 256#usize q1,
          List.ofFn (fun k : Fin 7 => source (c1 k.val)),sourceArray 64#usize fin) ∧
      Array.to_slice (array 256#usize q1) = alloc.vec.Vec.deref vq ∧
      Array.to_slice (array 64#usize fin) = alloc.vec.Vec.deref vf ∧
      (∀ j, j < 7 → canonical (c0 j) ∧ canonical (c1 j)) ∧ (∀ j, j < 64 → canonical (fin j)) := by
  obtain ⟨c0,hc0,holdc0,hcc0⟩ := PV_RunJoin_RoundAssociation44.complete ops 1024#usize (by decide) q w hq hw
  obtain ⟨q1,vq,hq1,holdq1,hiq,hcq1,hdq1⟩ := PV_RunJoin_PrimalFirst44.complete ops q hq a ha
  obtain ⟨w1,vw,hw1,holdw1,hiw,hcw1,hdw1⟩ := PV_RunJoin_DualFirst44.complete ops w hw a ha
  obtain ⟨c1,hc1,holdc1,hcc1⟩ := PV_RunJoin_RoundSecond44.complete ops q1 w1 hcq1 hcw1
  obtain ⟨fin,vf,hfin,holdfin,hifin,hcfin,hdfin⟩ := PV_RunJoin_PrimalSecond44.complete ops q1 hcq1 b hb
  refine ⟨c0,q1,c1,fin,vq,vf,?_,?_,hiq,hifin,fun j hj => ⟨hcc0 j hj,hcc1 j hj⟩,hcfin⟩
  · simp only [run,hc0,hq1,hw1,bind_tc_ok,← hiq,← hiw,hc1,hfin]
  · simp only [ProverCommitOpeningKernel49.run,show (1024#usize).val / 4 = 256 from rfl,
      holdc0,holdq1,holdw1,holdc1,holdfin,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_OpeningKernel44
