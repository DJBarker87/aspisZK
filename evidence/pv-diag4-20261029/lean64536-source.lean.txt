import PV_DIAG4_RawWrite
/-! Native last_os_error does not format: errno_location, dereference, then
Repr::new_os. The FOREIGN location execution remains explicit; it is not
asserted to be input-free or to return normally. The load is modeled only on
valid pointer/memory associations; that source memory relation remains P/V370. -/
set_option autoImplicit false
namespace PV_DIAG4
open PV_DIAG3
variable {S : Type}
structure ErrnoOps (S : Type) where
 location : Op S Nat
 load : S → Nat → Fin (2^32)
def readErrno (o : ErrnoOps S) : Op S (Fin (2^32)) :=
 sequence o.location (fun address s => ⟨[],s,.value (o.load s address)⟩)
def lastOsError (o : ErrnoOps S) : Op S RawWriteError :=
 sequence (readErrno o) (fun code => PV_DIAG3.pure (.os code))
theorem errno_location_normal (o : ErrnoOps S) (s t : S) (events : List Event)
 (address : Nat) (h : o.location s = ⟨events,t,.value address⟩) :
 readErrno o s = ⟨events,t,.value (o.load t address)⟩ := by
 simp [readErrno,sequence,h,PV_DIAG3.bind,prepend]
#print axioms errno_location_normal
theorem last_error_normal (o : ErrnoOps S) (s t : S) (events : List Event)
 (address : Nat) (h : o.location s = ⟨events,t,.value address⟩) :
 lastOsError o s = ⟨events,t,.value (.os (o.load t address))⟩ := by
 simp [lastOsError,sequence,errno_location_normal o s t events address h,
 PV_DIAG3.bind,PV_DIAG3.pure,prepend]
#print axioms last_error_normal
theorem errno_location_panics (o : ErrnoOps S) (s t : S) (events : List Event)
 (p : Panic) (h : o.location s = ⟨events,t,.panic p⟩) :
 lastOsError o s = ⟨events,t,.panic p⟩ := by
 simp [lastOsError,readErrno,sequence,h,PV_DIAG3.bind]
#print axioms errno_location_panics
theorem errno_location_aborts (o : ErrnoOps S) (s t : S) (events : List Event)
 (c : Crash) (h : o.location s = ⟨events,t,.abort c⟩) :
 lastOsError o s = ⟨events,t,.abort c⟩ := by
 simp [lastOsError,readErrno,sequence,h,PV_DIAG3.bind]
#print axioms errno_location_aborts
theorem errno_location_diverges (o : ErrnoOps S) (s t : S) (events : List Event)
 (h : o.location s = ⟨events,t,.diverge⟩) :
 lastOsError o s = ⟨events,t,.diverge⟩ := by
 simp [lastOsError,readErrno,sequence,h,PV_DIAG3.bind]
#print axioms errno_location_diverges
end PV_DIAG4
