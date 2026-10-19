import AspisR1CuDots.Types
import CuSavingsArrayBuilder

/-! Universal shared arithmetic parameters, not axiom placeholders. Both
emitted programs use the same instance. No algebraic property, success or
equivalence is assumed of these operations. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CuDots

class Arithmetic where
  newDot : Result fast_pairing.EbyKDot
  push : fast_pairing.EbyKDot → field.wide_exact.WideExact → field.QM31 →
    Result ((core.result.Result Unit Unit) × fast_pairing.EbyKDot)
  finish : fast_pairing.EbyKDot → Result field.wide_exact.WideExact
  add : field.wide_exact.WideExact → field.wide_exact.WideExact →
    Result field.wide_exact.WideExact
  fromLimbs : Array U32 8#usize → Result (Option field.wide_exact.WideExact)
  toLimbs : field.wide_exact.WideExact → Result (Array U32 8#usize)
  reduce : U64 → Result field.M31
  decodeM : Array U8 4#usize → Result (Option field.M31)
  decodeQ : Slice U8 → Result (Option field.QM31)

abbrev fast_pairing.EbyKDot.new [Arithmetic] := Arithmetic.newDot
abbrev fast_pairing.EbyKDot.push [Arithmetic] := Arithmetic.push
abbrev fast_pairing.EbyKDot.finish [Arithmetic] := Arithmetic.finish
abbrev field.wide_exact.WideExact.add [Arithmetic] := Arithmetic.add
abbrev field.wide_exact.WideExact.from_limbs [Arithmetic] := Arithmetic.fromLimbs
abbrev field.wide_exact.WideExact.to_limbs [Arithmetic] := Arithmetic.toLimbs
abbrev field.M31.reduce_u64 [Arithmetic] := Arithmetic.reduce
abbrev field.M31.from_le_bytes [Arithmetic] := Arithmetic.decodeM
abbrev field.QM31.from_le_bytes [Arithmetic] := Arithmetic.decodeQ
abbrev core.array.from_fn := @AspisR1.CuSavingsArrayBuilder.build

#print axioms Arithmetic
#print axioms core.array.from_fn
end AspisR1CuDots
