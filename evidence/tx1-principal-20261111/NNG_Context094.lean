import NNG_Carriers094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Context094
open Aeneas Aeneas.Std Result NMT_tx1
structure Calls where
 c0 : Result aspis_core.field.wide_exact.WideExact
 c1 : (Slice Std.U8) → Result (core.result.Result transport.Variant
    verifier.Error)
 c2 : (Slice Std.U8) → Result (core.result.Result Unit verifier.Error)
 c3 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
(Slice Std.U8) → verifier.Prepared → (Array Std.U8 32#usize) →
    Std.Usize → H → Result (core.result.Result Unit verifier.Error)
 c4 : (Slice Std.U8) → verifier.Prepared → verifier.Accumulator → (Array
    aspis_core.field.wide_exact.WideExact 29#usize) → (Option (verifier.Phase
    → Result Unit)) → verifier.QueryGeometry → verifier.BatchedWeights
    → Std.Usize → Result (core.result.Result (verifier.Accumulator ×
    verifier.BatchedWeights) verifier.Error)
 c5 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → H → (Option (verifier.Phase → Result Unit)) → (Array
    aspis_core.field.wide_exact.WideExact 29#usize) → Result
    ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))
 c6 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
verifier.Prepared → verifier.Accumulator → (Slice Std.U8) → (Slice
    Std.U8) → H → Result (alloc.vec.Vec Std.U8)
 c7 : verifier.BatchedWeights → (Slice aspis_core.field.QM31) → Result (Slice
    aspis_core.field.QM31)
 c8 : (Slice aspis_core.field.QM31) → Result (core.result.Result
    verifier.BatchedWeights verifier.Error)
 c9 : (Array Std.U32 22#usize) → Std.Usize → Std.Usize → Result
    (core.result.Result verifier.QueryGeometry verifier.Error)
 c10 : transport.Variant → Result (core.result.Result verifier.Accumulator
    verifier.Error)
 c11 : (Option (verifier.Phase → Result Unit)) → verifier.Phase → Result Unit

def emitted (c : Calls) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (h : H) (obs : Option (verifier.Phase → Result Unit)) :=
 verifier.candidate.tx1 c.c0 c.c1 c.c2 c.c3 c.c4 c.c5 c.c6 c.c7 c.c8 c.c9 c.c10 c.c11 D pub publicBytes proof k h obs
end AspisR1.NNG_Context094
