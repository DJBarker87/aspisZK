import NJR_Cuts
set_option autoImplicit false
namespace NJR_ReaderCut
open Aeneas Aeneas.Std
abbrev K := VTop_Stages.aspis_core.field.QM31
abbrev Error := VTop_Stages.verifier.Error

/-- Payload transcription of NJR_parent::reader_backing K007--010. SAME
backing is an immutable slice equality, justified by native pointer+length and
arbitrary byte assertions. Ownership metadata and the actual Vec drop are
native observations, not a law derived from a pointer. 
Native source: NJR_parent.rs.txt, sha256 8cbf394e884584117bc5ec545546723403ab9a8ca81fe9d5a1b26f67a5295ca1, harness reader_backing.
Assertion transcription: `assert_eq!(r.at,self.at);
assert_eq!(log.calls,1);let seen=log.seen.unwrap();assert_eq!(seen.as_ptr(),log.expected.as_ptr());assert_eq!(seen.len(),1768);assert_eq!(seen[b],bytes[b]);
match result{Err(e)=>{assert_eq!(Some(e),err);assert!(log.freed);assert_eq!(log.freed_ptr,ptr);assert_eq!(log.freed_len,64);assert_eq!(log.freed_cap,cap);},Ok((out,cursor))=>{
assert!(err.is_none());assert!(!log.freed);assert_eq!(cursor,post);assert_eq!(out.as_ptr(),ptr);assert_eq!(out.capacity(),cap);assert_eq!(out.len(),64);
assert_eq!(kw(out[j]),expected);`
Native ownership/capacity facts stay in the certificate packet; no additional
model field, child success or endpoint equation is inferred here.
-/
def Cut (bytes observed : Slice U8) (cursor observedAt : Nat) (before : List K) (i : Nat)
 (reply : core.result.Result K Error) (readerPost : Nat)
 (result : core.result.Result (List K × Nat) Error) (freed : Bool) : Prop :=
 observed=bytes ∧ observedAt=cursor ∧
 match reply with
 | .Err e => result=.Err e ∧ freed=true
 | .Ok q => result=.Ok (before.set i q,readerPost) ∧ freed=false

/-- On the error prefix the owned vector does not escape; no suffix/store or
successful output is assumed. Success keeps the SAME vector and exact frame. -/
theorem error_prefix (bytes observed : Slice U8) (cursor observedAt : Nat) (before : List K) (i : Nat)
 (e : Error) (post : Nat) (result : core.result.Result (List K × Nat) Error)
 (freed : Bool) (cut : Cut bytes observed cursor observedAt before i (.Err e) post result freed) :
 observed=bytes ∧ observedAt=cursor ∧ result=.Err e ∧ freed=true :=
 ⟨cut.1,cut.2⟩

/-- Each entered native step's arbitrary byte observation has a full immutable
backing frame. This is why the child domain applies to the parent's Reader. -/
theorem backing (bytes observed : Slice U8) (cursor observedAt : Nat) (before : List K) (i : Nat)
 (reply : core.result.Result K Error) (post : Nat)
 (result : core.result.Result (List K × Nat) Error) (freed : Bool)
 (cut : Cut bytes observed cursor observedAt before i reply post result freed) (j : Nat) :
 observed.val[j]?=bytes.val[j]? := by rw [cut.1]

#print axioms error_prefix
#print axioms backing
end NJR_ReaderCut
