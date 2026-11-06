import NKV_TreeTotal
import NKV_ErrorKinds
set_option autoImplicit false
noncomputable section
namespace NKV_TreeErrors
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

def Allowed : Result (Reply × Indices × Values) → Prop
 | .ok (r,_,_) => NKV_ErrorKinds.Allowed r | .fail _ => True | .div => True

theorem returned_allowed (out : Result Out) (valid : NKV_ErrorKinds.LoopAllowed out) :
 Allowed (out >>= returned) := by
 cases out with
 | fail e => trivial
 | div => trivial
 | ok out => exact valid

theorem classified (H : Bytes → HashState) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : Array U8 32#usize) (batch kind : Usize) (hb : batch.val<2) (hk : kind.val<3)
 (canonical : ∀ j,j<22 → raw.val[j]!.val<262144) (idx : Indices) (val : Values) :
 Allowed (NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ()) := by
 obtain ⟨keys,length,stream,entry⟩:=NKV_TreeEntry.source H proof raw root batch kind hb hk canonical idx val
 rw [entry]
 have bound:=(NKB_KeyStream.positive batch.val).2
 have valid:=NKV_ErrorKinds.loop (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) ()
   proof root kind (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) keys bound idx val 0#usize 0#usize
 simp only [NKV_ConcreteChildren.installed] at valid
 exact returned_allowed _ valid

/-- Complete direct reference returns a genuine Rust Result, and its ONLY
error constructors are Parse and Merkle. No accepted-input premise. -/
theorem complete (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : Array U8 32#usize) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (idx : Indices) (val : Values) :
 ∃ r i v,NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ()=ok (r,i,v) ∧ NKV_ErrorKinds.Allowed r := by
 obtain ⟨r,i,v,run⟩:=NKV_TreeTotal.source H proof len p wire raw root batch kind hb hk canonical idx val
 have valid:=classified H proof raw root batch kind hb hk canonical idx val
 rw [run] at valid
 exact ⟨r,i,v,run,valid⟩

/-- Source boundary part of (bb)(2)(b), explicitly at consumer rejection
observation. It does not assert the false literal direct duplicate-Err=fail
identity and does not yet install the complete frozen native invocation. -/
theorem error_iff (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : Array U8 32#usize) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (idx : Indices) (val : Values) :
 reject (Port3_NativeBatchBody.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ())=fail .panic ↔
 ∃ e i v,(e=verifier.Error.Parse ∨ e=verifier.Error.Merkle) ∧
 NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ()=ok (.Err e,i,v) := by
 rw [NKV_ConcreteChildren.source H proof raw root batch kind hb idx val]
 constructor
 · intro rejected
   obtain ⟨r,i,v,run,valid⟩:=complete H proof len p wire raw root batch kind hb hk canonical idx val
   rw [run] at rejected
   cases r with
   | Ok u => cases rejected
   | Err e => exact ⟨e,i,v,valid,run⟩
 · rintro ⟨e,i,v,allowed,run⟩
   rw [run]
   rfl

set_option pp.proofs false
#print classified
#print complete
#print error_iff
#print axioms returned_allowed
#print axioms classified
#print axioms complete
#print axioms error_iff
end NKV_TreeErrors
end
