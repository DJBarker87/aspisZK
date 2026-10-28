import LPi_TowerValues
set_option autoImplicit false
namespace AspisR1.NCH_OpaqueProduct
open Aeneas Aeneas.Std Result LPi_FieldValues

/-- Universal native flow over an unconstrained reply can be instantiated
with the emitted multiplication result. The caller still proves both domains.
The premise is universal in the reply, never a chosen successful product. -/
theorem instantiate (x y : NE) (hx : canonE x) (hy : canonE y)
    (post : NE → Prop) (flow : ∀ reply, post reply) :
    ∃ reply, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok reply ∧
      canonE reply ∧ ew reply=mulE (ew x) (ew y) ∧ post reply := by
  obtain ⟨reply,call,canonical,value⟩ := LPi_TowerValues.wide_mul x y hx hy
  exact ⟨reply,call,canonical,value,flow reply⟩

#print axioms instantiate
end AspisR1.NCH_OpaqueProduct
