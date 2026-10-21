import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1WeightsPairCut
@[reducible] def field.M31 := Std.U32
structure field.CM31 where
  a : field.M31
  b : field.M31
structure field.QM31 where
  c0 : field.CM31
  c1 : field.CM31
structure field.WideExact where
  c0 : field.QM31
  c1 : field.QM31
structure fast_pairing.canonical.Dot where
  sums : Array Std.U64 4#usize
structure fast_pairing.EbyKDot where
  c0 : fast_pairing.canonical.Dot
  c1 : fast_pairing.canonical.Dot
  count : Std.Usize
end AspisR1WeightsPairCut
