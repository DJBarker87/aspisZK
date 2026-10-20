import CuSavingsCanonicalInputPowers
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalInputHandback
open Aeneas Aeneas.Std Result AspisR1CanonicalInputs

theorem mutable_builder_projection {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F) :
    (do let (values,_)←AspisR1CanonicalInputs.core.array.from_fn_mut N inst state
        .ok values)=AspisR1.CuSavingsArrayBuilder.build N inst state := by
  unfold AspisR1CanonicalInputs.core.array.from_fn_mut AspisR1.CuSavingsArrayBuilder.build
  cases h : AspisR1.CuSavingsArrayBuilder.cells inst N.val 0#usize state <;> rfl

theorem array_source_admission {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F) :
    AspisR1CuArrayGraph.core.array.from_fn N inst state=
      AspisR1.CuSavingsArrayBuilder.build N inst state :=
  CuSavingsArrayFromFn.source_eq_build N inst state

#print axioms mutable_builder_projection
#print axioms array_source_admission
end AspisR1.CuSavingsCanonicalInputHandback
