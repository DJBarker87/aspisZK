import R1Z.PV_RDCD3_V260Exact

namespace R1Z.PV_RDCD3_V260
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_B2_253c1
abbrev K := aspis_core.field.QM31

/-- Exact raw method API, all weights/kinds/indices and complete Result.
Native structural association is recorded separately as reclassification within
existing compiler/Aeneas tool trust, never endpoint premise removal. -/
theorem source (w : host_weights.Weights) (kind j : Usize) :
    host_weights.Weights.raw w kind j = PV_RDCD3_V260Exact.original w kind j :=
  PV_RDCD3_V260Exact.source w kind j

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | ok x => ok (f x)
  | fail e => fail e
  | div => div

/-- Carrier projection preserves every error/divergence branch. -/
theorem carrier {B : Type} (decode : K → B) (w : host_weights.Weights) (kind j : Usize) :
    mapResult decode (host_weights.Weights.raw w kind j) =
      mapResult decode (PV_RDCD3_V260Exact.original w kind j) :=
  congrArg (mapResult decode) (source w kind j)

/-- Invalid D lookup fails before the checked inactive/unwrap continuation. -/
theorem invalid_D (w : host_weights.Weights) (j : Usize)
    (variant : w.variant = transport.Variant.D) (invalid : 1024 ≤ j.val) :
    host_weights.Weights.raw w 0#usize j = fail .arrayOutOfBounds := by
  rw [source]
  simp only [PV_RDCD3_V260Exact.original,if_true,PV_RDCD3_V260Exact.inactive,
    variant,PV_RDCD3_V260RowResult.invalid_D j invalid,bind_tc_fail]

#print axioms source
#print axioms carrier
#print axioms invalid_D
end R1Z.PV_RDCD3_V260
