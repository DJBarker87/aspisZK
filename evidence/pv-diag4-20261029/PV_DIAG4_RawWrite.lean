import PV_DIAG4_Interrupted
import PV_DIAG3_Write
/-! Concrete pure slots of raw Linux stderr write_all. The libc write and
last_os_error/errno executions remain explicit external operations. Requested
and delivered prefixes are carried by the syscall, never synthesized here. -/
set_option autoImplicit false
namespace PV_DIAG4
open PV_DIAG3
variable {S : Type}
inductive RawWriteError where
 | os (codeBits : Fin (2^32))
 | writeZero
 deriving DecidableEq, Repr
structure RawWriteOps (S : Type) where
 syscall : Nat → Bytes → Nat → Op S Int
 lastError : Op S (Fin (2^32))
 slicePanic : Bytes → Nat → Op S (Except RawWriteError Unit)
def linuxReadLimit : Nat := 2^63 - 1
def castUsize64 (r : Int) : Nat := (r % (2^64 : Int)).toNat
def rawGuard : RawWriteError → Op S Bool
 | .os code => osInterrupted code
 | .writeZero => PV_DIAG3.pure false
def rawErrorDrop : RawWriteError → Op S Unit
 | .os _ => PV_DIAG3.pure ()
 | .writeZero => PV_DIAG3.pure ()
def rawCvt (o : RawWriteOps S) (r : Int) : Op S (Except RawWriteError Nat) :=
 if r = -1 then sequence o.lastError (fun code => PV_DIAG3.pure (.error (.os code)))
 else PV_DIAG3.pure (.ok (castUsize64 r))
def rawFdWrite (o : RawWriteOps S) (fd : Nat) (buf : Bytes) : Op S (Except RawWriteError Nat) :=
 sequence (o.syscall fd buf (min buf.length linuxReadLimit)) (rawCvt o)
def linuxStderr (o : RawWriteOps S) : WriteOps S RawWriteError :=
 ⟨rawFdWrite o 2,.writeZero,rawGuard,rawErrorDrop,o.slicePanic⟩
theorem raw_error_drop_no_operation (e : RawWriteError) :
 (rawErrorDrop e : Op S Unit) = PV_DIAG3.pure () := by cases e <;> rfl
#print axioms raw_error_drop_no_operation
theorem raw_cvt_minus_one (o : RawWriteOps S) :
 rawCvt o (-1) = sequence o.lastError (fun code => PV_DIAG3.pure (.error (.os code))) := by
 simp [rawCvt]
#print axioms raw_cvt_minus_one
theorem raw_cvt_other (o : RawWriteOps S) (r : Int) (h : r ≠ -1) :
 rawCvt o r = PV_DIAG3.pure (.ok (castUsize64 r)) := by simp [rawCvt,h]
#print axioms raw_cvt_other
theorem raw_write_count (o : RawWriteOps S) (buf : Bytes) :
 (linuxStderr o).write buf = sequence (o.syscall 2 buf (min buf.length linuxReadLimit)) (rawCvt o) := rfl
#print axioms raw_write_count
theorem write_zero_guard_false (s : S) : rawGuard .writeZero s = ⟨[],s,.value false⟩ := rfl
#print axioms write_zero_guard_false
theorem raw_interrupted_retry (o : RawWriteOps S) (buf : Bytes)
 (next : Bytes → Op S (Except RawWriteError Unit)) (s t : S) (events : List Event)
 (code : Fin (2^32)) (hc : code.val = 4) (hne : buf.isEmpty = false)
 (hw : rawFdWrite o 2 buf s = ⟨events,t,.value (.error (.os code))⟩) :
 writeAllStep (linuxStderr o) buf next s = prepend events (next buf t) := by
 simp [writeAllStep,linuxStderr,hne,hw,sequence,PV_DIAG3.bind,rawGuard,
 osInterrupted,hc,PV_DIAG3.pure,rawErrorDrop,prepend]
#print axioms raw_interrupted_retry
end PV_DIAG4
