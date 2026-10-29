import R1Z.PV_RunJoin_RoundScaleThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundScaleCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_RoundScaleThread44 (W)
variable [t : ExternalTypes]

theorem phase (left right : ExternalFuns) (hs : left.op49=right.op49)
    (n : Nat) (c : Array W 7#usize) (lane : Usize) :
    @PV_RunJoin_RoundScaleThread44.phase t left n c lane=
      @PV_RunJoin_RoundScaleThread44.phase t right n c lane := by
  induction n generalizing c lane with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_RoundScaleThread44.phase,PV_RunJoin_RoundScaleThread44.step,
      aspis_core.field.wide_exact.WideExact.mul_m31,hs,ih]

theorem complete (left right : ExternalFuns) (hs : left.op49=right.op49) (c : Array W 7#usize) :
    @prover.round_loop1 t left c 0#usize=@prover.round_loop1 t right c 0#usize := by
  rw [@PV_RunJoin_RoundScaleThread44.complete t left c 0#usize 7 (by decide),
    @PV_RunJoin_RoundScaleThread44.complete t right c 0#usize 7 (by decide)]
  exact phase left right hs _ c _
#print axioms phase
#print axioms complete
end R1Z.PV_RunJoin_RoundScaleCongruence48
