import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LayoutConstants64
open Aeneas Aeneas.Std Result ProverRwFull

theorem fibres : aspis_core.r0.FIBRE_COUNT=ok 262144#usize := by
  unfold aspis_core.r0.FIBRE_COUNT
  decide

theorem words : aspis_core.r0.WORD_LEN=ok 1048576#usize := by
  unfold aspis_core.r0.WORD_LEN
  decide

#print axioms fibres
#print axioms words
end R1Z.PV_RunJoin_LayoutConstants64
