import NNG_verify_finish.Funs
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Emitted
open Aeneas Aeneas.Std Result NNG_verify_finish
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize
abbrev Claims := Array (Array Q 29#usize) 3#usize
abbrev K29 := Array Q 29#usize
abbrev Observer := Option (verifier.Phase → Result Unit)
abbrev Output (H : Type) := core.result.Result (r1_semantic.Verified H) r1_wire.Error
/-- The fresh emitted opaque interfaces. No field is a theorem or assumption
that a child succeeds; complete outer and inner Results remain explicit.
This compilation interface must be concretely instantiated before a root. -/
structure Calls where
 c0 : ∀ {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst :
  core.ops.function.FnMut F Std.Usize T),
  F → Result (Array T N)
 c1 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F),
  (core.result.Result T E) → O → Result (core.result.Result T F)
 c2 : aspis_core.circle.SecureCirclePoint → aspis_core.circle.SecureCirclePoint
  → Result Bool
 c3 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool
 c4 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result
  aspis_core.field.QM31
 c5 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result
  aspis_core.field.QM31
 c6 : (Array aspis_core.field.QM31 16#usize) → (Array aspis_core.field.QM31
  10#usize) → aspis_core.field.QM31 → (Array aspis_core.field.QM31
  10#usize) → Result aspis_core.field.QM31
 c7 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Array
  (Array aspis_core.field.QM31 29#usize) 3#usize) → (Array
  aspis_core.field.QM31 10#usize) →
  aspis_core.state_only_prefix.r0.Challenges → Result (core.result.Result
  aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)
 c8 : r1_wire.Prefix → Result (core.result.Result (Array (Array
  aspis_core.field.QM31 29#usize) 3#usize) r1_wire.Error)
 c9 : (Option (verifier.Phase → Result Unit)) → Std.U8 → Result Unit
 c10 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
  r1_wire.Prefix → (r1_wire.SemanticTranscript H) → Result
  (core.result.Result (aspis_core.field.QM31 × (Array aspis_core.field.QM31
  10#usize) × (r1_wire.SemanticTranscript H)) r1_wire.Error)
 c11 : r1_wire.Prefix → Std.U8 → Result (core.result.Result
  r1_wire.ValidatedRecord r1_wire.Error)
 c12 : r1_wire.Prefix → Std.U8 → Result (core.result.Result (Slice Std.U8)
  r1_wire.Error)
 c13 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
  (r1_wire.SemanticTranscript H) → r1_wire.ValidatedRecord → Result
  ((core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error) ×
  (r1_wire.SemanticTranscript H))
 c14 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
  (r1_wire.SemanticTranscript H) → Result (Array Std.U8 32#usize)
 c15 : ∀ (N : Std.Usize),
  r1_wire.ValidatedRecord → Std.Usize → Result (core.result.Result (Array
  aspis_core.field.QM31 N) r1_wire.Error)
  
/-- Original input and world retained once for every lexical continuation.
Typed NMT_CallTree.Event records arguments and complete replies. -/
structure Parent (H W : Type) where
 digest : aspis_core.digest.Digest32 H
 publicValue : Public
 prefixValue : r1_wire.Prefix
 transcript : r1_wire.SemanticTranscript H
 challenges : aspis_core.state_only_prefix.r0.Challenges
 observer : Observer
 world : W

def emitted {H W : Type} (c : Calls) (s : Parent H W) : Result (Output H) :=
 NNG_verify_finish.r1_semantic.verify_finish c.c0 c.c1 c.c2 c.c3 c.c4 c.c5 c.c6 c.c7 c.c8 c.c9 c.c10 c.c11 c.c12 c.c13 c.c14 c.c15
  s.digest s.publicValue s.prefixValue s.transcript s.challenges s.observer
end AspisR1.NNG_Emitted
