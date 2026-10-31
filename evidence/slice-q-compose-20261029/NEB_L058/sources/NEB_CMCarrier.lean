import NEB_CMCalls
set_option autoImplicit false
namespace NEB_CMCarrier
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem lossless (x : U32) :
    (core.convert.num.FromU64U32.from x).val=x.val := by scalar_tac

/-- The four actual u64::from arguments in the frozen complex product body. -/
theorem actual_casts (x y : NC) :
    (core.convert.num.FromU64U32.from x.a).val=x.a.val ∧
    (core.convert.num.FromU64U32.from x.b).val=x.b.val ∧
    (core.convert.num.FromU64U32.from y.a).val=y.a.val ∧
    (core.convert.num.FromU64U32.from y.b).val=y.b.val :=
  ⟨lossless _,lossless _,lossless _,lossless _⟩

#print axioms lossless
#print axioms actual_casts
end NEB_CMCarrier
