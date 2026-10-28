import R1Z.PV_RunJoin_RoundScaleThread44
import R1Z.PV_RunJoin_IntervalMap44
import R1Z.PV_RunJoin_SourceUpdate44
import R1Z.ProverCommitWideScalar48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundScaleValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]
def product (x : Raw) := ProverCommitWideScalar48.product x 536870912#u32

theorem step (ops : ExternalFuns) (xs : Nat → Raw) (i : Usize) (hi : i.val < 7) :
    @PV_RunJoin_RoundScaleThread44.step _ (ProverRwP6BodyCandidate.selected ops) (array 7#usize xs) i =
      .ok (array 7#usize (Function.update xs i.val (product (xs i.val)))) := by
  unfold PV_RunJoin_RoundScaleThread44.step
  have read : Array.index_usize (array 7#usize xs) i = .ok (current (source (xs i.val))) :=
    ProverCommitArray49.index 7#usize (fun k => current (source (xs k))) i hi
  rw [read]
  simp only [bind_tc_ok,weights.QUARTER]
  rw [PV_RunJoin_WideArithmetic44.scale ops _ _ _ (ProverCommitWideScalar48.source_exact (xs i.val) 536870912#u32).1]
  simp only [bind_tc_ok]
  exact PV_RunJoin_SourceUpdate44.update 7#usize xs i hi _

theorem phase (ops : ExternalFuns) (xs : Nat → Raw) (i : Usize) (n : Nat) (bound : i.val + n = 7) :
    @PV_RunJoin_RoundScaleThread44.phase _ (ProverRwP6BodyCandidate.selected ops) n (array 7#usize xs) i =
      .ok (array 7#usize (PV_RunJoin_IntervalMap44.map product xs i.val n)) := by
  induction n generalizing xs i with
  | zero =>
    change Result.ok (array 7#usize xs) = _
    rw [PV_RunJoin_IntervalMap44.zero]
  | succ n ih =>
    change (do
      let next ← @PV_RunJoin_RoundScaleThread44.step _ (ProverRwP6BodyCandidate.selected ops) (array 7#usize xs) i
      @PV_RunJoin_RoundScaleThread44.phase _ (ProverRwP6BodyCandidate.selected ops) n next (Usize.wrapping_add i 1#usize)) = _
    rw [step ops xs i (by omega)]
    simp only [bind_tc_ok]
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    rw [ih _ _ (by rw [inc];omega),inc,PV_RunJoin_IntervalMap44.step]

theorem complete (ops : ExternalFuns) (xs : Nat → Raw) :
    @prover.round_loop1 _ (ProverRwP6BodyCandidate.selected ops) (array 7#usize xs) 0#usize =
      .ok (array 7#usize (fun k => product (xs k))) := by
  rw [@PV_RunJoin_RoundScaleThread44.complete _ (ProverRwP6BodyCandidate.selected ops) _ 0#usize 7 (by rfl),phase ops xs 0#usize 7 (by rfl)]
  apply congrArg Result.ok
  apply Subtype.ext
  dsimp only [array,ProverCommitArray49.array]
  apply congrArg List.ofFn
  funext k
  have h : 0 ≤ k.val ∧ k.val < 0+7 := ⟨Nat.zero_le _,k.isLt⟩
  simp only [PV_RunJoin_IntervalMap44.map,show (0#usize).val=0 from rfl,if_pos h]
#print axioms step
#print axioms phase
#print axioms complete
end R1Z.PV_RunJoin_RoundScaleValue44
