import AspisR1CanonicalDots.Types
import AspisR1CuRho.FunsExternal
import AspisR1CanonicalStd.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CanonicalDots
/-! Computational source leaves only. No property of array-map, iteration,
canonicality or source equivalence is postulated. Standard library body
admission and canonical caller derivation remain separate obligations. -/
class Shared where
  raw : Array U32 4#usize → Array U32 4#usize → Result (Array U64 4#usize)
  add : field.QM31 → field.QM31 → Result field.QM31
  mul : field.QM31 → field.QM31 → Result field.QM31
abbrev core.array.Array.map := @AspisR1CuRho.core.array.Array.map
abbrev core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all := @AspisR1CanonicalStd.all
abbrev core.option.Option.ok_or := @AspisR1CanonicalStd.ok_or
abbrev field.QM31.add [Shared] := Shared.add
abbrev field.QM31.mul [Shared] := Shared.mul
abbrev new_pairing.canonical.Q.raw [Shared] := Shared.raw
abbrev old_pairing.canonical.Q.raw [Shared] := Shared.raw
#print axioms Shared
end AspisR1CanonicalDots
