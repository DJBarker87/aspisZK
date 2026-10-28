import NDO_JHb_S2K_Equality

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.Equality
open AspisR1TerminalDecoder

theorem array_ne_self {T : Type} (cmp : core.cmp.PartialEq T T)
    (same : ∀ x, cmp.ne x x = ok false) {n : Usize} (a : Array T n) :
    core.array.equality.PartialEqArray.ne cmp a a = ok false := by
  rw [core.array.equality.PartialEqArray.ne,array_self cmp same]
  rfl

theorem u8_ne_self (x : U8) : core.cmp.PartialEqU8.ne x x = ok false := by
  simp [core.cmp.PartialEqU8,core.cmp.impls.PartialEqU8.ne,liftFun2,lift]

theorem m31_ne_self (x : aspis_core.field.M31) :
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x x = ok false := by
  simp [aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]


#print axioms array_ne_self
#print axioms u8_ne_self
#print axioms m31_ne_self
end AspisR1.S2K.Equality
