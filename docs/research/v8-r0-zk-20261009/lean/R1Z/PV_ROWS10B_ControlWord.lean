import R1Z.PV_ROWS10B_Dispatch
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_ControlWord
/-- Explicit control alphabet. These are external events, never inferred
from successful-byte uniformity. Ordering/caches belong to the source link. -/
inductive Site where
  | pointerLoad | dlsym | probe | pointerStore
  | fdLoad | compareExchange | futexWait | openRandom | pollRandom
  | closeRandom | openUrandom | fdStore | futexWake | getrandom | read
  deriving DecidableEq, Repr
structure Request where
  site : Site
  amount : Nat
  flags : Int
  deriving DecidableEq, Repr
structure SysWord where
  returned : Int
  errno : Int
  deriving DecidableEq, Repr
/-- Linux's getrandom Error representation: OS errors negative; the two
internal errors used here are INTERNAL_START+1 and INTERNAL_START+2. -/
def lastError (errno : Int) : Int := if 0 < errno then -errno else 65537
inductive FillStep where
  | advance (count : Nat)
  | retry
  | error (code : Int)
  deriving DecidableEq, Repr
/-- ret is a native signed-size result, so a positive result converts to
usize on the same x86_64 target. The boundary must preserve that typing. -/
def sysStep (remaining : Nat) (reply : SysWord) : FillStep :=
  if 0 < reply.returned then
    if reply.returned.toNat ≤ remaining then .advance reply.returned.toNat else .error 65538
  else if reply.returned = -1 then
    if reply.errno = 4 then .retry else .error (lastError reply.errno)
  else .error 65538

inductive Progress where
  | success
  | error (code : Int)
  | pending (remaining : Nat)
  deriving DecidableEq, Repr
/-- A finite tape is a finite prefix. Pending is NOT divergence. -/
def run : List SysWord → Nat → Progress
  | _, 0 => .success
  | [], n+1 => .pending (n+1)
  | reply::tail, n+1 =>
    match sysStep (n+1) reply with
    | .advance count => run tail (n+1-count)
    | .retry => run tail (n+1)
    | .error e => .error e
/-- Genuine nontermination of this control model requires EVERY finite
prefix to remain pending, not merely a short tape. -/
def Diverges (tape : Nat → SysWord) (remaining : Nat) : Prop :=
  ∀ fuel, ∃ n, run ((List.range fuel).map tape) remaining = .pending n

inductive FdAction where
  | lock
  | compareExchange
  | wait
  | use (fd : Int)
  deriving DecidableEq, Repr

def fdEntry (fd : Int) : FdAction :=
  if fd = -1 ∨ fd = -2 then .lock else .use fd

def fdLock (fd : Int) : FdAction :=
  if fd = -1 then .compareExchange else if fd = -2 then .wait else .use fd

def fdPublish : Except Int Int → Int
  | .ok fd => fd
  | .error _ => -1

inductive OpenStep where
  | opened (fd : Int)
  | retry
  | error (code : Int)
  deriving DecidableEq, Repr

def openStep (reply : SysWord) : OpenStep :=
  if 0 ≤ reply.returned then .opened reply.returned
  else if reply.errno = 4 then .retry else .error (lastError reply.errno)

inductive PollStep where
  | closeThen (result : Except Int Unit)
  | retry
  deriving DecidableEq, Repr

def pollStep (reply : SysWord) : PollStep :=
  if 0 ≤ reply.returned then .closeThen (.ok ())
  else if reply.errno = 4 then .retry else .closeThen (.error (lastError reply.errno))

/-- The full public boundary word must include initialization and cache
scheduling events as well as getrandom/read results. Matching draw length
alone is strictly insufficient. This is a P interface, not added T. -/
def PV_ROWS10B_Link_ActualControlPublic {W C : Type}
    (word : W → C → List (Request × SysWord)) : Prop :=
  ∀ a b c, word a c = word b c

theorem success_conversion (returned : Int) (positive : 0 < returned) :
    Int.ofNat returned.toNat = returned := Int.toNat_of_nonneg (by omega)

theorem eio : sysStep 64 ⟨-1, 5⟩ = .error (-5) := rfl
theorem eintr : sysStep 64 ⟨-1, 4⟩ = .retry := rfl
theorem invalid_errno : sysStep 64 ⟨-1, 0⟩ = .error 65537 := rfl
theorem invalid_count : sysStep 64 ⟨65, 0⟩ = .error 65538 := rfl
theorem zero_return : sysStep 64 ⟨0, 0⟩ = .error 65538 := rfl
theorem invalid_negative : sysStep 64 ⟨-2, 0⟩ = .error 65538 := rfl
theorem partial_then_error : run [⟨16,0⟩,⟨-1,5⟩] 64 = .error (-5) := rfl
theorem interrupted_then_success : run [⟨-1,4⟩,⟨64,0⟩] 64 = .success := rfl
theorem short_tape_is_pending : run [⟨-1,4⟩] 64 = .pending 64 := rfl
theorem failed_fd_initialization (e : Int) : fdPublish (.error e) = -1 := rfl
theorem successful_fd_initialization (fd : Int) : fdPublish (.ok fd) = fd := rfl
theorem fd_initial : fdEntry (-1) = .lock ∧ fdLock (-1) = .compareExchange := ⟨rfl,rfl⟩
theorem fd_ongoing : fdEntry (-2) = .lock ∧ fdLock (-2) = .wait := ⟨rfl,rfl⟩
theorem poll_error_closes : pollStep ⟨-1,12⟩ = .closeThen (.error (-12)) := rfl
theorem poll_interrupt_retries : pollStep ⟨-1,4⟩ = .retry := rfl
theorem open_interrupt_retries : openStep ⟨-1,4⟩ = .retry := rfl

/-- Equal requests allow both of these real-source-compatible control words;
the native loader experiment checks the EIO path. This is not a witness
counterexample to privacy, and makes no statement about T's densities. -/
theorem fixed64_does_not_fix_signal :
    run [⟨64,0⟩] 64 ≠ run [⟨-1,5⟩] 64 := by decide

#print axioms success_conversion
#print axioms eio
#print axioms eintr
#print axioms invalid_errno
#print axioms invalid_count
#print axioms zero_return
#print axioms invalid_negative
#print axioms partial_then_error
#print axioms interrupted_then_success
#print axioms short_tape_is_pending
#print axioms failed_fd_initialization
#print axioms successful_fd_initialization
#print axioms fd_initial
#print axioms fd_ongoing
#print axioms poll_error_closes
#print axioms poll_interrupt_retries
#print axioms open_interrupt_retries
#print axioms fixed64_does_not_fix_signal
end R1Z.PV_ROWS10B_ControlWord
