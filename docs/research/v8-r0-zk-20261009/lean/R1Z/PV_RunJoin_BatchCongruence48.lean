import R1Z.PV_RunJoin_BatchRowCongruence48
import R1Z.PV_RunJoin_BatchThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_BatchRowThread44 (W Coefficients)
variable [t : ExternalTypes]

theorem phase (left right : ExternalFuns)
    (hz : left.op42=right.op42) (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (coefficients : Coefficients) (gp : Array W 29#usize) (n : Nat) (q : alloc.vec.Vec W) (row : Usize) :
    @PV_RunJoin_BatchThread44.phase t left coefficients gp n q row=
      @PV_RunJoin_BatchThread44.phase t right coefficients gp n q row := by
  induction n generalizing q row with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_BatchThread44.phase,PV_RunJoin_BatchThread44.step,
      PV_RunJoin_BatchRowCongruence48.complete left right hz hm ha,ih]

theorem complete (left right : ExternalFuns)
    (hz : left.op42=right.op42) (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (hp : @ExternalFuns.op254 t left=@ExternalFuns.op254 t right)
    (coefficients : Coefficients) (g : W) :
    @prover.opening_batch t left coefficients g=@prover.opening_batch t right coefficients g := by
  rw [@PV_RunJoin_BatchThread44.caller t left,@PV_RunJoin_BatchThread44.caller t right]
  simp only [weights.powers,hp,phase left right hz hm ha]
#print axioms phase
#print axioms complete
end R1Z.PV_RunJoin_BatchCongruence48
