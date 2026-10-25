import T2Nat_ResultEq
import Port5Q2_ReaderScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ScalarJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq
abbrev Unwrap := T2Nat_RawJoin.Unwrap

def raw (unwrap : Unwrap) := fun N => Port5Q2_ReaderRaw.raw N (unwrap N)
def readK (unwrap : Unwrap) := Port5Q2_ReaderScalar.readK (raw unwrap) Port5Q2_ReaderScalar.decodeK
def readE (unwrap : Unwrap) := Port5Q2_ReaderScalar.readE (raw unwrap) Port5Q2_ReaderScalar.decodeE

theorem raw_eq (unwrap : Unwrap) (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (N : Usize) (r : verifier.Reader) :
    EqOk (raw unwrap N r) (CheckpointBytes3Reader.raw N r) :=
  T2Nat_RawJoin.success_iff N unwrap unwrap_ok r

/-- Full scalar return (including Checkpoint errors) and reader carrier,
with no caller-supplied bound or independently selected read success. -/
theorem k_eq (unwrap : Unwrap) (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (r : verifier.Reader) : EqOk (readK unwrap r) (CheckpointBytes3Reader.readK r) := by
  rw [← Port5Q2_ReaderScalar.reference_k r]
  unfold readK Port5Q2_ReaderScalar.readK
  exact T2Nat_ResultEq.bind (raw_eq unwrap unwrap_ok 16#usize r) (fun _ => T2Nat_ResultEq.refl _)

theorem e_eq (unwrap : Unwrap) (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (r : verifier.Reader) : EqOk (readE unwrap r) (CheckpointBytes3Reader.readE r) := by
  rw [← Port5Q2_ReaderScalar.reference_e r]
  unfold readE Port5Q2_ReaderScalar.readE
  exact T2Nat_ResultEq.bind (raw_eq unwrap unwrap_ok 32#usize r) (fun _ => T2Nat_ResultEq.refl _)

#print axioms raw_eq
#print axioms k_eq
#print axioms e_eq
end AspisR1.T2Nat_ScalarJoin
end
