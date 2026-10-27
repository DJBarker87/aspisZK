import JGj_ZeroSubtract
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ZeroLifted
open Aeneas Aeneas.Std Result FIq_Native
def source (x : U64) (y : U32) : Result U64 := do
  let p ← lift (core.convert.num.FromU64U32.from field.P)
  let withP ← x+p
  let wide ← lift (core.convert.num.FromU64U32.from y)
  withP-wide
theorem factor (x : U64) (y : U32) : source x y=JGj_ZeroSubtract.source x y := by rfl
#print axioms factor
end AspisR1.JGj_ZeroLifted
end
