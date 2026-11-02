import PV_EVH_IOErrorOsBits
set_option autoImplicit false
namespace PV_EVH_IOErrorOsControl
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes)

/-- last_os_error reads the reached thread's errno, then constructs the OS
variant. This is source-control/value semantics, not full native observation
adequacy. TLS read, pointer/bit-operation association and L3 stay explicit P. -/
def lastError (readErrno : Q Int) : Q Nat := do
  let code ← readErrno
  pure (PV_EVH_IOErrorOsBits.encode code)

def osInterrupted (code : Int) : Bool := decide (code = 4)
def osBadFd (code : Int) : Bool := decide (code = 9)

theorem current_errno (readErrno : Q Int) (w : State) (code : Int)
    (h : (readErrno w).outcome = .returned (.ok code)) :
    lastError readErrno w =
      ⟨.returned (.ok (PV_EVH_IOErrorOsBits.encode code)),
        (readErrno w).state,(readErrno w).events⟩ := by
  simp only [lastError,Bind.bind,PV_EVH_Runtime.bind,h,Pure.pure,
    PV_EVH_Runtime.lift,List.append_nil]

/-- No pre-write errno is read. Both raw-write and errno-read prefixes and
world updates are preserved, with precisely the OS variant in the result.
This does not install a native libc/TLS instance or a complete io::Error type. -/
theorem after_write (libc : Nat → Nat → Nat → Bytes → Q Int)
    (readErrno : Q Int) (fd address : Nat) (bytes : Bytes) (w : State) (code : Int)
    (hw : (libc fd address (PV_EVH_FileDescWrite.count bytes) bytes w).outcome =
      .returned (.ok (-1)))
    (he : (readErrno (libc fd address (PV_EVH_FileDescWrite.count bytes) bytes w).state).outcome =
      .returned (.ok code)) :
    PV_EVH_FileDescWrite.write libc (lastError readErrno) fd address bytes w =
      ⟨.returned (.ok (.error (PV_EVH_IOErrorOsBits.encode code))),
        (readErrno (libc fd address (PV_EVH_FileDescWrite.count bytes) bytes w).state).state,
        (libc fd address (PV_EVH_FileDescWrite.count bytes) bytes w).events ++
          (readErrno (libc fd address (PV_EVH_FileDescWrite.count bytes) bytes w).state).events⟩ := by
  simp only [PV_EVH_FileDescWrite.write,Bind.bind,PV_EVH_Runtime.bind,hw,if_true,
    current_errno readErrno _ code he,Pure.pure,PV_EVH_Runtime.lift,List.append_nil]

/-- The reached OS code survives packing and decoding, including negative
i32 codes; no host-word wrapping or unsigned truncation changes classification. -/
theorem classifications (code : Int) (lo : -(2^31 : Int) ≤ code)
    (hi : code < (2^31 : Int)) :
    osInterrupted (PV_EVH_IOErrorOsBits.decode (PV_EVH_IOErrorOsBits.encode code)) =
      osInterrupted code ∧
    osBadFd (PV_EVH_IOErrorOsBits.decode (PV_EVH_IOErrorOsBits.encode code)) = osBadFd code := by
  rw [PV_EVH_IOErrorOsBits.roundtrip code lo hi]
  exact ⟨rfl,rfl⟩

#print axioms current_errno
#print axioms after_write
#print axioms classifications
end PV_EVH_IOErrorOsControl
