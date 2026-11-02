import PV_EVH_LiteralWriteAll
set_option autoImplicit false
namespace PV_EVH_FileDescWrite
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes)

/-- Linux x86_64 READ_LIMIT is isize::MAX. This is the requested bound, not a
claim that libc delivered the whole request. -/
def readLimit : Nat := 2^63-1
def count (bytes : Bytes) : Nat := min bytes.length readLimit

/-- Rust's signed64 to usize64 cast is modular, not Int.toNat on negatives.
Only -1 is the cvt error sentinel. Native signed-register validity stays P. -/
def castCount (r : Int) : Nat := (r % (2^64 : Int)).toNat

/-- FileDesc::write's exact libc request and cvt/map control. Both the raw
write and last_os_error are WORLD operations; the latter sees the post-write
errno. Actual libc ABI/buffer, error representation and error drop remain P. -/
def write {E : Type}
    (libc : Nat → Nat → Nat → Bytes → Q Int) (lastError : Q E)
    (fd address : Nat) (bytes : Bytes) : Q (Except E Nat) := do
  let r ← libc fd address (count bytes) bytes
  if r = -1 then
    let e ← lastError
    pure (.error e)
  else pure (.ok (castCount r))

theorem bounded_request (bytes : Bytes) :
    count bytes ≤ bytes.length ∧ count bytes ≤ readLimit :=
  ⟨Nat.min_le_left _ _,Nat.min_le_right _ _⟩

theorem error_world {E : Type}
    (libc : Nat → Nat → Nat → Bytes → Q Int) (lastError : Q E)
    (fd address : Nat) (bytes : Bytes) (w : State)
    (h : (libc fd address (count bytes) bytes w).outcome = .returned (.ok (-1))) :
    write libc lastError fd address bytes w =
      let next := PV_EVH_Runtime.bind lastError
        (fun e => PV_EVH_Runtime.lift (.ok (Except.error e : Except E Nat)))
        (libc fd address (count bytes) bytes w).state
      ⟨next.outcome,next.state,
        (libc fd address (count bytes) bytes w).events ++ next.events⟩ := by
  simp only [write,Bind.bind,PV_EVH_Runtime.bind,h,if_true,
    Pure.pure,PV_EVH_Runtime.lift]

theorem nonerror_world {E : Type}
    (libc : Nat → Nat → Nat → Bytes → Q Int) (lastError : Q E)
    (fd address : Nat) (bytes : Bytes) (w : State) (r : Int)
    (h : (libc fd address (count bytes) bytes w).outcome = .returned (.ok r))
    (hr : r ≠ -1) :
    write libc lastError fd address bytes w =
      ⟨.returned (.ok (.ok (castCount r))),
        (libc fd address (count bytes) bytes w).state,
        (libc fd address (count bytes) bytes w).events⟩ := by
  simp only [write,Bind.bind,PV_EVH_Runtime.bind,h,hr,if_false,
    Pure.pure,PV_EVH_Runtime.lift,List.append_nil]

theorem fault_prefix {E : Type}
    (libc : Nat → Nat → Nat → Bytes → Q Int) (lastError : Q E)
    (fd address : Nat) (bytes : Bytes) (w : State) (e : Fault)
    (h : (libc fd address (count bytes) bytes w).outcome = .fault e) :
    write libc lastError fd address bytes w =
      ⟨.fault e,(libc fd address (count bytes) bytes w).state,
        (libc fd address (count bytes) bytes w).events⟩ := by
  simp only [write,Bind.bind,PV_EVH_Runtime.bind,h]

#print axioms bounded_request
#print axioms error_world
#print axioms nonerror_world
#print axioms fault_prefix
end PV_EVH_FileDescWrite
