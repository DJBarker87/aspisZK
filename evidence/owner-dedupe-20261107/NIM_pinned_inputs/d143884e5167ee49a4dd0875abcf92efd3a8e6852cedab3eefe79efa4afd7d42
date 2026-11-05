import NGU_Part004
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_Oracle
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

/-- Full child log: neither partial sums nor count are omitted. -/
structure Entry where
 value : NE
 scalar : NQ
 before : Native
 after : Native
 reply : core.result.Result Unit Unit

inductive Control where
 | advance (lane : Nat)
 | parse (lane : Nat)

/-- Transcription of Rust f_ref after its checked selection ports. -/
def G (lane : Nat) (before after : Native) (value : NE) (scalar : NQ)
 (reply : core.result.Result Unit Unit) : Control × Native × List Entry :=
 (match reply with | .Ok _ => .advance (lane+1) | .Err _ => .parse lane,
  after,[⟨value,scalar,before,after,reply⟩])

/-- Source-shaped local oracle, with both child Result arms. -/
def reference (lane : Nat) (before after : Native) (value : NE) (scalar : NQ)
 (reply : core.result.Result Unit Unit) : Control × Native × List Entry :=
 let entry : Entry := ⟨value,scalar,before,after,reply⟩
 match reply with
 | .Ok _ => (.advance (lane+1),after,[entry])
 | .Err _ => (.parse lane,after,[entry])

theorem reference_eq_G (lane : Nat) (before after : Native) (value : NE) (scalar : NQ)
 (reply : core.result.Result Unit Unit) :
 reference lane before after value scalar reply=G lane before after value scalar reply := by
 cases reply <;> rfl

/-- Instantiate the child from its total checked law; no output equality is a premise. -/
theorem child (lane : Nat) (before : Native) (value : NE) (scalar : NQ)
 (cv : canonE value) (cq : canonQ scalar) (count : before.count.val<29) :
 ∃ after, FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (.Ok (),after) ∧
  NGU_LPm_PointLoop.ops.pushDot (statePort before) (ePort value) (qPort scalar)=
   ok (.Ok (),statePort after) ∧
  reference lane before after value scalar (.Ok ())=
   (.advance (lane+1),after,[⟨value,scalar,before,after,.Ok ()⟩]) := by
 obtain ⟨after,native,model⟩ := NGU_LPm_PublicPort.source before value scalar cv cq (by omega)
 exact ⟨after,native,model,rfl⟩

/-- Every immutable frame value is retained, including unread Verified fields. -/
def framed {A : Type} (frame : A) (lane : Nat) (before after : Native)
 (value : NE) (scalar : NQ) (reply : core.result.Result Unit Unit) :=
 (frame,reference lane before after value scalar reply)

theorem frame {A : Type} (original : A) (lane : Nat) (before after : Native)
 (value : NE) (scalar : NQ) (reply : core.result.Result Unit Unit) :
 (framed original lane before after value scalar reply).1=original := rfl

#print axioms reference_eq_G
#print axioms child
#print axioms frame
end AspisR1.NGY_Oracle
end
