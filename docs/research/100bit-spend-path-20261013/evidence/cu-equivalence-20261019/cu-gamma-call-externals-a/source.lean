import AspisR1CuGammaCall.Types

/-! Explicit shared unchanged caller boundaries. The two preparation symbols
and powers are the actual imported, checked gamma declarations, not axioms. -/
set_option autoImplicit false
namespace AspisR1CuGamma
open Aeneas Aeneas.Std Result
class CallerBoundaries where
  verifyObserved : {H : Type} → aspis_core.Digest32 H →
    pool_v1.pair_forest_semantic_terminal.r0.Public → Slice U8 → H →
    Option (verifier.Phase → Result Unit) → Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  parse : Slice U8 → Result (core.result.Result verifier.View verifier.Error)
  accumulatorNew : transport.Variant → Result (core.result.Result verifier.Accumulator verifier.Error)
  finish : {H : Type} → aspis_core.Digest32 H → verifier.View → verifier.Prepared → verifier.Accumulator →
    Array aspis_core.field.WideExact 29#usize → Slice U8 → Slice U8 → Usize → H →
    Option (verifier.Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)

abbrev r1_semantic.verify_observed [CallerBoundaries] := @CallerBoundaries.verifyObserved _
abbrev verifier.View.parse [CallerBoundaries] := CallerBoundaries.parse
abbrev verifier.Accumulator.new [CallerBoundaries] := CallerBoundaries.accumulatorNew
abbrev verifier.tx1_finish [CallerBoundaries] := @CallerBoundaries.finish _

#print axioms CallerBoundaries
#print axioms gamma_old.Prepared.gamma_old_new
#print axioms gamma_new.Prepared.gamma_new_new
end AspisR1CuGamma
