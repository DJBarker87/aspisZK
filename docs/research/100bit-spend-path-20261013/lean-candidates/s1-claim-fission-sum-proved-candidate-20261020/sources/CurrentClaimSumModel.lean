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
@[discriminant isize]
inductive verifier.Error where
| Parse : verifier.Error
| Semantic : verifier.Error
| Transcript : verifier.Error
| Relation : verifier.Error
| Merkle : verifier.Error
| Query : verifier.Error
| Checkpoint : verifier.Error
| Allocation : verifier.Error

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


namespace Concrete
abbrev E := aspis_core.field.WideExact
abbrev Full := AspisR1CurrentWide.Proof.E

def toCM (x : aspis_core.field.CM31) : AspisR1CurrentWide.field.CM31 := ⟨x.a,x.b⟩
def toQM (x : aspis_core.field.QM31) : AspisR1CurrentWide.field.QM31 := ⟨toCM x.c0,toCM x.c1⟩
def toFull (x : E) : Full := ⟨toQM x.c0,toQM x.c1⟩
def fromCM (x : AspisR1CurrentWide.field.CM31) : aspis_core.field.CM31 := ⟨x.a,x.b⟩
def fromQM (x : AspisR1CurrentWide.field.QM31) : aspis_core.field.QM31 := ⟨fromCM x.c0,fromCM x.c1⟩
def fromFull (x : Full) : E := ⟨fromQM x.c0,fromQM x.c1⟩
theorem to_from (x : Full) : toFull (fromFull x)=x := by cases x; rfl
theorem from_to (x : E) : fromFull (toFull x)=x := by cases x; rfl
def Canonical (x : E) : Prop := AspisR1CurrentWide.Proof.CanonicalWide (toFull x)
def decode (x : E) := AspisR1CurrentWide.Proof.decodeWide (toFull x)
end Concrete

def aspis_core.field.WideExact.add (x y : Concrete.E) : Result Concrete.E := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.add (Concrete.toFull x) (Concrete.toFull y)
  ok (Concrete.fromFull z)
def aspis_core.field.WideExact.mul (x y : Concrete.E) : Result Concrete.E := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.mul (Concrete.toFull x) (Concrete.toFull y)
  ok (Concrete.fromFull z)

namespace Concrete
 theorem add_total_exact (x y : E) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.WideExact.add x y = .ok z ∧ Canonical z ∧ decode z=decode x+decode y := by
  obtain ⟨z,hz,hc,he⟩ := AspisR1CurrentWide.Proof.wide_add_total_exact (toFull x) (toFull y) hx hy
  refine ⟨fromFull z,?_,?_,?_⟩
  · simp only [aspis_core.field.WideExact.add,hz,bind_tc_ok]
  · simpa only [Canonical,to_from] using hc
  · simpa only [decode,to_from] using he
 theorem mul_total_exact (x y : E) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.WideExact.mul x y = .ok z ∧ Canonical z ∧ decode z=decode x*decode y := by
  obtain ⟨z,hz,hc,he⟩ := AspisR1CurrentWide.Proof.wide_mul_total_exact (toFull x) (toFull y) hx hy
  refine ⟨fromFull z,?_,?_,?_⟩
  · simp only [aspis_core.field.WideExact.mul,hz,bind_tc_ok]
  · simpa only [Canonical,to_from] using hc
  · simpa only [decode,to_from] using he
end Concrete
/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_sum]: loop body 0:
    Source: 'lib.rs', lines 755:8-755:95 -/
@[rust_loop_body]
def verifier.prepared_claim_sum_loop.body
  (k : Array aspis_core.field.WideExact 7#usize)
  (parts : Array aspis_core.field.WideExact 7#usize)
  (iter : core.ops.range.Range Std.Usize) (claim : aspis_core.field.WideExact)
  :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    aspis_core.field.WideExact) aspis_core.field.WideExact)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done claim)
  | some i =>
    let we ← Array.index_usize parts i
    trace.value 14#u16 i we
    let we1 ← Array.index_usize k i
    let we2 ← aspis_core.field.WideExact.mul we1 we
    let claim1 ← aspis_core.field.WideExact.add claim we2
    ok (cont (iter1, claim1))

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_sum]: loop 0:
    Source: 'lib.rs', lines 755:8-755:95 -/
@[rust_loop]
def verifier.prepared_claim_sum_loop
  (iter : core.ops.range.Range Std.Usize)
  (k : Array aspis_core.field.WideExact 7#usize)
  (parts : Array aspis_core.field.WideExact 7#usize)
  (claim : aspis_core.field.WideExact) :
  Result aspis_core.field.WideExact
  := do
  loop
    (fun (iter1, claim1) => verifier.prepared_claim_sum_loop.body k parts iter1
      claim1)
    (iter, claim)

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_sum]:
    Source: 'lib.rs', lines 753:0-758:1 -/
def verifier.prepared_claim_sum
  (k : Array aspis_core.field.WideExact 7#usize)
  (parts : Array aspis_core.field.WideExact 7#usize) :
  Result aspis_core.field.WideExact
  := do
  let claim ←
    verifier.prepared_claim_sum_loop { start := 0#usize, «end» := 7#usize } k
      parts aspis_core.field.WideExact.ZERO
  trace.value 14#u16 7#usize claim
  ok claim


#print axioms Concrete.add_total_exact
#print axioms Concrete.mul_total_exact
end AspisR1CurrentPreparedClaim
