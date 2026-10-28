import R1Z.PV_CompressLastPower
set_option autoImplicit false
namespace R1Z.PV_CompressArity
open Aeneas Aeneas.Std Result ProverRwFull

theorem length (values : Array aspis_core.field.M31 16#usize) :
    Slice.len (Array.to_slice values)=16#usize := by
  apply UScalar.eq_of_val_eq
  change values.val.length=16
  exact values.property

-- Site-local restriction: the actual retained source calls compression on this
-- typed array. A complete native equality/caller certificate remains required.
theorem restriction (left right : aspis_core.field.M31 → Slice aspis_core.field.M31 →
      aspis_core.field.QM31 → Result aspis_core.field.QM31)
    (agree : ∀ tag values lambda, Slice.len values=16#usize →
      left tag values lambda=right tag values lambda)
    (tag : aspis_core.field.M31) (values : Array aspis_core.field.M31 16#usize)
    (lambda : aspis_core.field.QM31) :
    left tag (Array.to_slice values) lambda=right tag (Array.to_slice values) lambda :=
  agree tag _ lambda (length values)
theorem values_length (values : Array aspis_core.field.M31 16#usize) :
    (Array.to_slice values).val.length=16 := values.property
#print axioms values_length
#print axioms length
#print axioms restriction
end R1Z.PV_CompressArity
