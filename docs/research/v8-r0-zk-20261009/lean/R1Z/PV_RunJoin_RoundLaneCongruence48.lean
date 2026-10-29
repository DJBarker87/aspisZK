import R1Z.PV_RunJoin_RoundCellCongruence48
import R1Z.PV_RunJoin_RoundLaneThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundLaneCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_RoundLaneThread44 (W)
variable [t : ExternalTypes]

theorem complete (left right : ExternalFuns)
    (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (q w : Slice W) (d : Usize) (n : Nat) (c : Array W 7#usize) (lane : Usize) :
    @PV_RunJoin_RoundLaneThread44.phase t left q w d n c lane=
      @PV_RunJoin_RoundLaneThread44.phase t right q w d n c lane := by
  induction n generalizing c lane with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_RoundLaneThread44.phase,PV_RunJoin_RoundLaneThread44.step,
      PV_RunJoin_RoundCellCongruence48.complete left right hm ha,ih]
#print axioms complete
end R1Z.PV_RunJoin_RoundLaneCongruence48
