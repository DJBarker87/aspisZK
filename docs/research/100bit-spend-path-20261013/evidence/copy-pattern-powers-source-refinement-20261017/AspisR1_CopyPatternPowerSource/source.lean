import AspisR1SelectedMaskProbe.Funs
import Aeneas.Tactic.RustAttributes

/-! Exact sealed indexed-candidate source partition. -/
set_option autoImplicit false
namespace AspisR1CopyPatternCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

@[global_simps, irreducible]
def poseidon2.POSEIDON2_WIDTH : Std.Usize := 16#usize

@[rust_loop]
def pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0
  (lambda : field.QM31) (powers : Array field.QM31 16#usize)
  (power : field.QM31) (limb : Std.Usize) :
  Result ((Array field.QM31 16#usize) × Std.Usize)
  := do
  if limb < poseidon2.POSEIDON2_WIDTH
  then
    let a ← Array.update powers limb power
    let power1 ← field.QM31.mul power lambda
    let limb1 ← limb + 1#usize
    pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0 lambda a
      power1 limb1
  else ok (powers, limb)
partial_fixpoint

end AspisR1CopyPatternCandidate
