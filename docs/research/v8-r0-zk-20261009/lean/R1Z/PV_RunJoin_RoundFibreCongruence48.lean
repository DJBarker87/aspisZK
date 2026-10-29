import R1Z.PV_RunJoin_RoundLaneCongruence48
import R1Z.PV_RunJoin_RoundFibreThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundFibreCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_RoundFibreThread44 (W)
variable [t : ExternalTypes]

theorem phase (left right : ExternalFuns)
    (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (q w : Slice W) (n : Nat) (c : Array W 7#usize) (lane : Usize) :
    @PV_RunJoin_RoundFibreThread44.phase t left q w n c lane=
      @PV_RunJoin_RoundFibreThread44.phase t right q w n c lane := by
  induction n generalizing c lane with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_RoundFibreThread44.phase,PV_RunJoin_RoundFibreThread44.step,
      PV_RunJoin_RoundLaneCongruence48.complete left right hm ha,ih]

theorem complete (left right : ExternalFuns)
    (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (q w : Slice W) (small : q.length/4≤256) (c : Array W 7#usize) :
    @prover.round_loop0 t left q w c 0#usize=@prover.round_loop0 t right q w c 0#usize := by
  rw [@PV_RunJoin_RoundFibreThread44.complete t left q w c 0#usize (q.length/4) (by omega) small,
    @PV_RunJoin_RoundFibreThread44.complete t right q w c 0#usize (q.length/4) (by omega) small]
  exact phase left right hm ha q w _ c _
#print axioms phase
#print axioms complete
end R1Z.PV_RunJoin_RoundFibreCongruence48
