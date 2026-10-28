import NDO_JGj_ZeroSubtract
import NDO_JGj_ScalarNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ZeroLiftedSymbolic
open Aeneas Aeneas.Std Result FIq_Native
def source (x : U64) (y : U32) : Result U64 := do
  let p ← lift (core.convert.num.FromU64U32.from field.P)
  let withP ← x+p
  let wide ← lift (core.convert.num.FromU64U32.from y)
  withP-wide
theorem factor (x : U64) (y : U32) : source x y=JGj_ZeroSubtract.source x y := by
  simp only [source,JGj_ZeroSubtract.source,lift,bind_tc_ok,JGj_ScalarNotation.wide,JGj_ScalarNotation.add,JGj_ScalarNotation.sub]
#print axioms factor
end AspisR1.JGj_ZeroLiftedSymbolic
end
