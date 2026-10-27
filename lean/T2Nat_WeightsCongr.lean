import T2Nat_ScalarJoin
import Port5Q2_ReaderWeightJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_WeightsCongr
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq
abbrev K := aspis_core.field.QM31

theorem reads (left right : CheckpointBytes4Sections.ReadK)
    (same : ∀ r, EqOk (left r) (right r)) (bytes : Slice U8) (n : Nat) (start : Usize) :
    EqOk (Port5Q2_ReaderWeights.reads left bytes n start)
      (Port5Q2_ReaderWeights.reads right bytes n start) := by
  induction n generalizing start with
  | zero => exact T2Nat_ResultEq.refl _
  | succ n ih =>
    unfold Port5Q2_ReaderWeights.reads
    apply T2Nat_ResultEq.bind (same _)
    intro pair
    rcases pair with ⟨value,next⟩
    cases value with
    | Err e => exact T2Nat_ResultEq.refl _
    | Ok x =>
      apply T2Nat_ResultEq.bind (ih next.at)
      intro rest
      exact T2Nat_ResultEq.refl _

theorem weights (left right : CheckpointBytes4Sections.ReadK)
    (same : ∀ r, EqOk (left r) (right r)) (bytes : Slice U8) (start : Usize)
    (v : alloc.vec.Vec K) :
    EqOk (Port5Q2_ReaderWeights.weights left bytes start v)
      (Port5Q2_ReaderWeights.weights right bytes start v) := by
  rw [Port5Q2_ReaderWeights.exact,Port5Q2_ReaderWeights.exact]
  exact T2Nat_ResultEq.bind (reads left right same bytes v.val.length start)
    (fun _ => T2Nat_ResultEq.refl _)

/-- Native scalar substitution composes through the entire mutable iterator
helper. It preserves every returned decoder error, Vec and cursor. -/
theorem native (unwrap : T2Nat_RawJoin.Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (start : Usize)
    (v : alloc.vec.Vec K) :
    EqOk (Port5Q2_ReaderWeights.weights (T2Nat_ScalarJoin.readK unwrap) bytes start v)
      (Port5Q2_ReaderWeights.weights CheckpointBytes3Reader.readK bytes start v) :=
  weights _ _ (T2Nat_ScalarJoin.k_eq unwrap unwrap_ok) bytes start v

#print axioms reads
#print axioms weights
#print axioms native
end AspisR1.T2Nat_WeightsCongr
end
