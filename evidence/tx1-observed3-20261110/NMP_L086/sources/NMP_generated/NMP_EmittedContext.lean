import NMP_prepare.Funs
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Emitted
open Aeneas Aeneas.Std Result NMP_prepare
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Observer := Option (verifier.Phase → Result Unit)
abbrev SemanticOut (H : Type) := core.result.Result (r1_semantic.Verified H) r1_wire.Error
abbrev Scratch := Array aspis_core.field.wide_exact.WideExact 29#usize
abbrev PreparedOut := core.result.Result verifier.Prepared verifier.Error × Scratch
/-- Exact fresh E002 opaque interfaces. Intermediate support only: every child
must be installed at its caller-established SAME argument before a row root. -/
structure Calls where
 c0 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
    core.ops.function.FnOnce O E F),
  (core.result.Result T E) → O → Result (core.result.Result T F)
 c1 : ∀ {T : Type} (coremarkerCopyInst : core.marker.Copy T),
  Std.Usize → T → Result (core.result.Result (alloc.vec.Vec T)
      aspis_core.r0.Error)
 c2 : (Slice Std.U8) → (Slice Std.U8) → (Slice Std.U8) → Result
      (core.result.Result verifier.View verifier.Error)
 c3 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
  (r1_semantic.Verified H) → verifier.View → H → (Array
      aspis_core.field.wide_exact.WideExact 29#usize) → Result
      ((core.result.Result verifier.Prepared verifier.Error) × (Array
      aspis_core.field.wide_exact.WideExact 29#usize))
 c4 : (Option (verifier.Phase → Result Unit)) → verifier.Phase → Result Unit
 c5 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
  r1_wire.Prefix → (r1_wire.SemanticTranscript H) → Result
      ((core.result.Result aspis_core.state_only_prefix.r0.Challenges
      r1_wire.Error) × (r1_wire.SemanticTranscript H))
 c6 : (Slice Std.U8) → Result (core.result.Result r1_wire.Prefix r1_wire.Error)
 c7 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
      r1_wire.Prefix → (r1_wire.SemanticTranscript H) →
      aspis_core.state_only_prefix.r0.Challenges → (Option (verifier.Phase →
      Result Unit)) → Result (core.result.Result (r1_semantic.Verified H)
      r1_wire.Error)
 c8 : (Option (verifier.Phase → Result Unit)) → Std.U8 → Result Unit
 c9 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → H →
      (Array Std.U8 32#usize) → Result (core.result.Result
      (r1_wire.SemanticTranscript H) r1_wire.Error)
 c10 : (Slice Std.U8) → (Slice Std.U8) → Result ((core.result.Result Unit
      compact.CodecError) × (Slice Std.U8))
 c11 : (Slice Std.U8) → (Slice Std.U8) → Result ((core.result.Result Unit
      compact.CodecError) × (Slice Std.U8))
/-- One parent state retains original arguments, the world and ordered site prefix.
The Code interpreter carries the full typed argument/reply event log.
No post-abort world or scratch is synthesized by this carrier. -/
structure Parent (H W : Type) where
 digest : aspis_core.digest.Digest32 H
 publicValue : Public
 bytes : Slice U8
 hash : H
 observer : Observer
 scratch : Scratch
 world : W
 sites : List String

def observed {H W : Type} (c : Calls) (s : Parent H W) : Result (SemanticOut H) :=
 NMP_prepare.r1_semantic.verify_observed c.c5 c.c6 c.c7 c.c8 c.c9
  s.digest s.publicValue s.bytes s.hash s.observer

def prepare {H W : Type} (c : Calls) (s : Parent H W) : Result PreparedOut :=
 NMP_prepare.verifier.candidate.prepare c.c0 c.c1 c.c2 c.c3 c.c4 c.c5 c.c6 c.c7 c.c8 c.c9 c.c10 c.c11
  s.digest s.publicValue s.bytes s.hash s.observer s.scratch
end AspisR1.NMP_Emitted
