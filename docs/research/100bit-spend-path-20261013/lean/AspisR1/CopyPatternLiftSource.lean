import AspisR1SelectedMaskProbe.Funs

/-! Exact sealed indexed-candidate source partition. -/
set_option autoImplicit false
namespace AspisR1CopyPatternCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

@[global_simps, irreducible] def field.M31.ZERO : field.M31 := 0#u32

@[global_simps, irreducible]
def field.CM31.ZERO : field.CM31 := { a := 0#u32, b := 0#u32 }

def field.CM31.from_m31 (a : field.M31) : Result field.CM31 := do
  ok { a, b := field.M31.ZERO }

def field.QM31.from_cm31 (c0 : field.CM31) : Result field.QM31 := do
  ok { c0, c1 := field.CM31.ZERO }

def pool_v1.pair_forest_copy_terminal.lift_m31
  (value : field.M31) : Result field.QM31 := do
  let c ← field.CM31.from_m31 value
  field.QM31.from_cm31 c

end AspisR1CopyPatternCandidate
