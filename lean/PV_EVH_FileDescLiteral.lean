import PV_EVH_FileDescWrite
set_option autoImplicit false
namespace PV_EVH_FileDescLiteral
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes)

/-- Native starting address belongs to the ORIGINAL literal. The retained
write_all suffix determines every later address, including repeated EINTR.
No address is inferred from byte equality, and no pointer provenance is proved
by this arithmetic. Error-kind/drop/constructor/bad-count remain world ops. -/
def driver {E : Type} (libc : Nat → Nat → Nat → Bytes → Q Int)
    (lastError : Q E) (interrupted : E → Q Bool) (dropInterrupted : E → Q Unit)
    (writeZero : Q E) (badCount : Nat → Bytes → Q (Except E Unit))
    (fd address : Nat) (original : Bytes) : PV_EVH_WriteAll.Driver where
  Error := E
  write := fun pending => PV_EVH_FileDescWrite.write libc lastError fd
    (address+(original.length-pending.length)) pending
  interrupted := interrupted
  dropInterrupted := dropInterrupted
  writeZero := writeZero
  badCount := badCount

theorem suffix_address (original : Bytes) (address offset : Nat)
    (h : offset ≤ original.length) :
    address+(original.length-(original.drop offset).length) = address+offset := by
  rw [List.length_drop]
  omega

theorem next_address (original : Bytes) (address offset n : Nat)
    (ho : offset ≤ original.length) (hn : n ≤ (original.drop offset).length) :
    address+(original.length-((original.drop offset).drop n).length) = address+offset+n := by
  simp only [List.length_drop] at hn ⊢
  omega

/-- The low-level request issued by the EXISTING stateful write_all Driver
has the exact suffix pointer. This supplies pointer advancement, not libc's
return/errno, the initial literal's address, or stderr lock adequacy. -/
theorem reached_write {E : Type} (libc : Nat → Nat → Nat → Bytes → Q Int)
    (lastError : Q E) (interrupted : E → Q Bool) (dropInterrupted : E → Q Unit)
    (writeZero : Q E) (badCount : Nat → Bytes → Q (Except E Unit))
    (fd address : Nat) (original : Bytes) (offset : Nat)
    (h : offset ≤ original.length) :
    (driver libc lastError interrupted dropInterrupted writeZero badCount fd address original).write
      (original.drop offset) = PV_EVH_FileDescWrite.write libc lastError fd
        (address+offset) (original.drop offset) := by
  simp only [driver,suffix_address original address offset h]

#print axioms suffix_address
#print axioms next_address
#print axioms reached_write
end PV_EVH_FileDescLiteral
