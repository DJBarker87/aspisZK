import R1Z.PV_RunJoin_BatchRowThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchRowCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_BatchRowThread44 (W Coefficients)
variable [t : ExternalTypes]

theorem phase (left right : ExternalFuns)
    (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (coefficients : Coefficients) (gp : Array W 29#usize) (row : Usize)
    (n : Nat) (lane : Usize) (value : W) :
    @PV_RunJoin_BatchRowThread44.phase t left coefficients gp row n lane value=
      @PV_RunJoin_BatchRowThread44.phase t right coefficients gp row n lane value := by
  induction n generalizing lane value with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_BatchRowThread44.phase,PV_RunJoin_BatchRowThread44.step,
      aspis_core.field.wide_exact.WideExact.mul,aspis_core.field.wide_exact.WideExact.add,hm,ha,ih]

theorem complete (left right : ExternalFuns)
    (hz : left.op42=right.op42) (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (coefficients : Coefficients) (gp : Array W 29#usize) (row : Usize) :
    @prover.opening_row t left coefficients gp row=@prover.opening_row t right coefficients gp row := by
  rw [@PV_RunJoin_BatchRowThread44.caller t left,@PV_RunJoin_BatchRowThread44.caller t right]
  simp only [aspis_core.field.wide_exact.WideExact.ZERO,hz,phase left right hm ha]
#print axioms phase
#print axioms complete
end R1Z.PV_RunJoin_BatchRowCongruence48
