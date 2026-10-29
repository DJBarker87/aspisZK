import R1Z.PV_RunJoin_FoldThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldCellCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FoldThread44 (W)
variable [t : ExternalTypes]

theorem complete (left right : ExternalFuns)
    (hm : left.op47=right.op47) (ha : left.op46=right.op46) (hs : left.op52=right.op52)
    (q : Array W 4#usize) (alpha : W) (dual : Bool) :
    @prover.fold_cell t left q alpha dual=@prover.fold_cell t right q alpha dual := by
  simp only [prover.fold_cell,aspis_core.field.wide_exact.WideExact.mul,
    aspis_core.field.wide_exact.WideExact.add,aspis_core.field.wide_exact.WideExact.mul_m31,hm,ha,hs]
#print axioms complete
end R1Z.PV_RunJoin_FoldCellCongruence48
