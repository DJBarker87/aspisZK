import R1Z.PV_RunJoin_RoundCellThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundCellCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_RoundCellThread44 (W)
variable [t : ExternalTypes]

theorem complete (left right : ExternalFuns)
    (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (q w : Slice W) (d s : Usize) (n : Nat) (c : Array W 7#usize) (lane : Usize) :
    @PV_RunJoin_RoundCellThread44.phase t left q w d s n c lane=
      @PV_RunJoin_RoundCellThread44.phase t right q w d s n c lane := by
  induction n generalizing c lane with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_RoundCellThread44.phase,PV_RunJoin_RoundCellThread44.step,
      aspis_core.field.wide_exact.WideExact.mul,aspis_core.field.wide_exact.WideExact.add,hm,ha,ih]
#print axioms complete
end R1Z.PV_RunJoin_RoundCellCongruence48
