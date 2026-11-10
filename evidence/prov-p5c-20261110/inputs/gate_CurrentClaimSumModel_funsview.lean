import CurrentWideLinearExact
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim

/-- [aspis_r1_verify_prepared_prefix::aspis_core::field::M31]
    Source: 'lib.rs', lines 88:0-88:24
    Visibility: public -/
@[reducible]
def aspis_core.field.M31 := Std.U32

/-- [aspis_r1_verify_prepared_prefix::aspis_core::field::CM31]
    Source: 'lib.rs', lines 56:0-59:1
    Visibility: public -/
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31

/-- [aspis_r1_verify_prepared_prefix::aspis_core::field::QM31]
    Source: 'lib.rs', lines 62:0-65:1
    Visibility: public -/
structure aspis_core.field.QM31 where
  c0 : aspis_core.field.CM31
  c1 : aspis_core.field.CM31

/-- [aspis_r1_verify_prepared_prefix::aspis_core::circle::SecureCirclePoint]
    Source: 'lib.rs', lines 10:0-13:1
    Visibility: public -/
structure aspis_core.circle.SecureCirclePoint where
  x : aspis_core.field.QM31
  y : aspis_core.field.QM31

/-- Trait declaration: [aspis_r1_verify_prepared_prefix::aspis_core::Digest32]
    Source: 'lib.rs', lines 16:0-18:1
    Visibility: public -/
structure aspis_core.Digest32 (Self : Type) where
  coremarkerCopyInst : core.marker.Copy Self
  digest : Self → Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)

/-- [aspis_r1_verify_prepared_prefix::aspis_core::field::WideExact]
    Source: 'lib.rs', lines 43:0-46:1
    Visibility: public -/
structure aspis_core.field.WideExact where
  c0 : aspis_core.field.QM31
  c1 : aspis_core.field.QM31

/-- [aspis_r1_verify_prepared_prefix::r1_wire::Challenges]
    Source: 'lib.rs', lines 452:4-459:5
    Visibility: public -/
structure r1_wire.Challenges where
  lambda : aspis_core.field.QM31
  chi : aspis_core.field.QM31
  theta : aspis_core.field.QM31
  zc : Array aspis_core.field.QM31 10#usize
  mu : aspis_core.field.QM31
  eta : aspis_core.field.QM31

/-- [aspis_r1_verify_prepared_prefix::r1_wire::SemanticTranscript]
    Source: 'lib.rs', lines 557:0-561:1
    Visibility: public -/
structure r1_wire.SemanticTranscript (H : Type) where
  state : Array Std.U8 32#usize
  hash : H
  next_row : Std.U8

/-- [aspis_r1_verify_prepared_prefix::r1_semantic::Verified]
    Source: 'lib.rs', lines 629:0-645:1
    Visibility: public -/
structure r1_semantic.Verified (H : Type) where
  roots : Array (Array Std.U8 32#usize) 2#usize
  challenges : r1_wire.Challenges
  alpha : Array aspis_core.field.QM31 10#usize
  claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize
  extra : Array aspis_core.field.QM31 29#usize
  before_z1 : Array aspis_core.field.QM31 29#usize
  state_before_z0 : Array Std.U8 32#usize
  z : Array aspis_core.circle.SecureCirclePoint 2#usize
  transcript : r1_wire.SemanticTranscript H

/-- [aspis_r1_verify_prepared_prefix::verifier::Error]
    Source: 'lib.rs', lines 733:0-740:38
    Visibility: public -/
inductive verifier.Error where
| Parse : verifier.Error
| Semantic : verifier.Error
| Transcript : verifier.Error
| Relation : verifier.Error
| Merkle : verifier.Error
| Query : verifier.Error
| Checkpoint : verifier.Error
| Allocation : verifier.Error

-- Naming-only expansion of the pinned Aeneas discriminant generator.
def verifier.Error.read_discriminant (x : verifier.Error) : Isize :=
  match x with
  | .Parse => 0#isize
  | .Semantic => 1#isize
  | .Transcript => 2#isize
  | .Relation => 3#isize
  | .Merkle => 4#isize
  | .Query => 5#isize
  | .Checkpoint => 6#isize
  | .Allocation => 7#isize

instance _root_.AspisR1CurrentPreparedClaim.verifier.Error.instDiscriminant :
    Aeneas.Std.Discriminant verifier.Error Isize where
  read_discriminant := verifier.Error.read_discriminant

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot::closure]
    Source: 'lib.rs', lines 763:38-763:53 -/
@[reducible]
def verifier.prepared_claim_dot.closure (H : Type) := Unit

@[global_simps, irreducible]
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_r1_verify_prepared_prefix::aspis_core::field::{aspis_r1_verify_prepared_prefix::aspis_core::field::WideExact}::ZERO]
    Source: 'lib.rs', lines 48:4-51:6
    Visibility: public -/
@[global_simps, irreducible]
def aspis_core.field.WideExact.ZERO : aspis_core.field.WideExact :=
  { c0 := aspis_core.field.QM31.ZERO, c1 := aspis_core.field.QM31.ZERO }

/-- [aspis_r1_verify_prepared_prefix::trace::value]:
    Source: 'lib.rs', lines 714:0-719:1
    Visibility: public -/
def trace.value
  (tag : Std.U16) (index : Std.Usize) (x : aspis_core.field.WideExact) :
  Result Unit
  := do
  ok ()


end AspisR1CurrentPreparedClaim
