import R1Z.ProverRwSuccessField
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessConstants
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
-- Native source: multiproof LEAF_BITS=18, MAX_BATCH=16;
-- r1_wire POINTS=3, LANES=29, CLAIMS=POINTS*LANES.
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessField.selected ops with
    op235 := .ok 18#u32, op236 := .ok 16#usize,
    op239 := .ok 87#usize, op240 := .ok 29#usize}

theorem leaf_bits (ops : ExternalFuns) : (selected ops).op235 = .ok 18#u32 := rfl
theorem max_batch (ops : ExternalFuns) : (selected ops).op236 = .ok 16#usize := rfl
theorem claims (ops : ExternalFuns) : (selected ops).op239 = .ok 87#usize := rfl
theorem lanes (ops : ExternalFuns) : (selected ops).op240 = .ok 29#usize := rfl
#print axioms leaf_bits
#print axioms max_batch
#print axioms claims
#print axioms lanes
end R1Z.ProverRwSuccessConstants
