import AspisR1DelayedDots.Types
import CuSavingsArrayBuilder
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1DelayedDots
/- Shared unchanged computations, universally quantified, with no proposition
fields. Changed arithmetic, decoder and limb projection remain actual source. -/
class Shared where
  newDot : Result fast_pairing.EbyKDot
  push : fast_pairing.EbyKDot → field.wide_exact.WideExact → field.QM31 →
    Result ((core.result.Result Unit Unit) × fast_pairing.EbyKDot)
  finish : fast_pairing.EbyKDot → Result field.wide_exact.WideExact
  add : field.wide_exact.WideExact → field.wide_exact.WideExact → Result field.wide_exact.WideExact
  fromLimbs : Array U32 8#usize → Result (Option field.wide_exact.WideExact)
  branch : {T : Type} → Option T → Result (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)
  residual : (T : Type) → Option core.convert.Infallible → Result (Option T)
abbrev fast_pairing.EbyKDot.new [Shared] := Shared.newDot
abbrev fast_pairing.EbyKDot.push [Shared] := Shared.push
abbrev fast_pairing.EbyKDot.finish [Shared] := Shared.finish
abbrev field.wide_exact.WideExact.add [Shared] := Shared.add
abbrev field.wide_exact.WideExact.from_limbs [Shared] := Shared.fromLimbs
abbrev core.option.Option.Insts.CoreOpsTry_traitTry.branch [Shared] := @Shared.branch _
abbrev core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual [Shared] := Shared.residual
abbrev core.array.from_fn := @AspisR1.CuSavingsArrayBuilder.build
#print axioms Shared
end AspisR1DelayedDots
