import R1Z.PV_RunJoin_FoldCellCongruence48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FoldThread44 (W)
variable [t : ExternalTypes]

theorem phase (left right : ExternalFuns)
    (hm : left.op47=right.op47) (ha : left.op46=right.op46) (hs : left.op52=right.op52)
    (q : Slice W) (alpha : W) (dual : Bool) (n : Nat) (out : alloc.vec.Vec W) (i : Usize) :
    @PV_RunJoin_FoldThread44.phase t left q alpha dual n out i=
      @PV_RunJoin_FoldThread44.phase t right q alpha dual n out i := by
  induction n generalizing out i with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_FoldThread44.phase,PV_RunJoin_FoldThread44.step,
      PV_RunJoin_FoldCellCongruence48.complete left right hm ha hs,ih]

theorem complete (left right : ExternalFuns)
    (hm : left.op47=right.op47) (ha : left.op46=right.op46) (hs : left.op52=right.op52)
    (q : Slice W) (alpha : W) (dual : Bool) (small : q.length/4≤256) :
    @prover.fold t left q alpha dual=@prover.fold t right q alpha dual := by
  rw [@PV_RunJoin_FoldThread44.caller t left q alpha dual small,
    @PV_RunJoin_FoldThread44.caller t right q alpha dual small]
  simp only [phase left right hm ha hs]
#print axioms phase
#print axioms complete
end R1Z.PV_RunJoin_FoldCongruence48
