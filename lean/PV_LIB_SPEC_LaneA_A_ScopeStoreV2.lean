import PV_LIB_A_StorePrimitiveV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ScopeStoreV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_LIB_A_StorePrimitiveV2
/-- ONE named source meaning for thread:f457, std/thread/scoped.rs48-60.
The overflow branch increments, invokes overflow(), decrements(false), then
panics. Its net source count is the old count; it is not the normal increment.
All world/events and the original full reply remain external to this Store
projection. No unpark can occur in this overflow decrement: the incremented
count would equal1 only if the old count were0, which is not overflow. -/
def PV_THR2_LibrarySemantics_ScopeIncrement457 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference] => modifyNumber C s w reference [0,0,0]
      (fun old => if old > modulus/2-1 then old else (old+1)%modulus)
  | _ => none

/-- ONE named source meaning for thread:f611, std/thread/scoped.rs63-70.
The bool field is AtomicBool/UnsafeCell<u8>; it is written before fetch_sub.
main_thread.unpark's backend effects are kept in the original native reply.
This does not claim source/runtime adequacy of an arbitrary Thread codec. -/
def PV_THR2_LibrarySemantics_ScopeDecrement611 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  match args with
  | [reference,.boolean panic] =>
    let changed ← if panic then put C s w reference [1,0,0] (.number 1) else some s
    modifyNumber C changed w reference [0,0,0] (fun old => (old+modulus-1)%modulus)
  | _ => none

/-- The overflow control branch is derived from source arithmetic, rather than
requiring an overflow-free caller Pre. -/
theorem overflow_restores (n : Nat) (overflow : modulus/2-1 < n) :
    (if n > modulus/2-1 then n else (n+1)%modulus) = n := if_pos overflow

/-- Even on the overflow branch, the final fetch_sub cannot choose unpark. -/
theorem overflow_not_last (n : Nat) (fits : n < modulus)
    (overflow : modulus/2-1 < n) : (n+1)%modulus ≠ 1 := by
  have positive : 0 < modulus := by decide
  have large : 1 < modulus := by decide
  by_cases top : n+1 = modulus
  · rw [top,Nat.mod_self]
    decide
  · have bounded : n+1 < modulus := by omega
    rw [Nat.mod_eq_of_lt bounded]
    have nz : n ≠ 0 := by
      intro z
      subst n
      have bound : 0 < modulus/2-1 := by decide
      omega
    omega

#print axioms PV_THR2_LibrarySemantics_ScopeIncrement457
#print axioms PV_THR2_LibrarySemantics_ScopeDecrement611
#print axioms overflow_restores
#print axioms overflow_not_last
end PV_LIB_A_ScopeStoreV2
