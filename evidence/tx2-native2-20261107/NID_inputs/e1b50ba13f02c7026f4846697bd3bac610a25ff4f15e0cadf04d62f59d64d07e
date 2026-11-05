import NID_ResumeCanonical
import T2Nat_ReaderJoin
set_option autoImplicit false
noncomputable section
namespace NID_BoundedReaders
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Upgrade the retained EqOk bridge to exact full Result only where actual
caller bounds make the reference raw read outer-total. Inner Checkpoint errors
remain ordinary values. No fail/div equivalence is inferred from EqOk alone. -/
theorem k (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (r : verifier.Reader)
 (bound : r.at.val+16≤r.bytes.val.length) :
 T2Nat_ScalarJoin.readK unwrap r=CheckpointBytes3Reader.readK r := by
 obtain ⟨b,out,_,_,_,run⟩ := CheckpointBytes3Reader.read_k_c5 r bound
 exact ((T2Nat_ScalarJoin.k_eq unwrap unwrap_ok r _).mpr run).trans run.symm

theorem e (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (r : verifier.Reader)
 (bound : r.at.val+32≤r.bytes.val.length) :
 T2Nat_ScalarJoin.readE unwrap r=CheckpointBytes3Reader.readE r := by
 obtain ⟨b,out,_,_,_,run⟩ := CheckpointBytes3Reader.read_e_c5 r bound
 exact ((T2Nat_ScalarJoin.e_eq unwrap unwrap_ok r _).mpr run).trans run.symm

/-- Every actual weight iteration is within the SAME checkpoint backing. -/
theorem weight (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (r : verifier.Reader) (i : Nat)
 (size : r.bytes.val.length=1768) (cursor : r.at.val=712+16*i) (inside : i<64) :
 T2Nat_ScalarJoin.readK unwrap r=CheckpointBytes3Reader.readK r :=
 k unwrap unwrap_ok r (by rw [cursor,size];omega)

theorem semantic (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (r : verifier.Reader) (i : Nat)
 (size : r.bytes.val.length=1768) (cursor : r.at.val=408+16*i) (inside : i<10) :
 T2Nat_ScalarJoin.readK unwrap r=CheckpointBytes3Reader.readK r :=
 k unwrap unwrap_ok r (by rw [cursor,size];omega)
#print axioms k
#print axioms e
#print axioms weight
#print axioms semantic
end NID_BoundedReaders
