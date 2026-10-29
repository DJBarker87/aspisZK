import R1Z.PV_RunJoin_RoundFibreCongruence48
import R1Z.PV_RunJoin_RoundScaleCongruence48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundCongruence48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_RoundCellThread44 (W)
variable [t : ExternalTypes]

theorem complete (left right : ExternalFuns)
    (hz : left.op42=right.op42) (hm : left.op47=right.op47)
    (ha : left.op46=right.op46) (hs : left.op52=right.op52)
    (q w : Slice W) (small : q.length/4≤256) :
    @prover.round t left q w=@prover.round t right q w := by
  simp only [prover.round,aspis_core.field.wide_exact.WideExact.ZERO,hz,
    PV_RunJoin_RoundFibreCongruence48.complete left right hm ha q w small,
    PV_RunJoin_RoundScaleCongruence48.complete left right hs]
#print axioms complete
end R1Z.PV_RunJoin_RoundCongruence48
