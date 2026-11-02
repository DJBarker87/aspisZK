import PV_EVH_LinuxRawHistory
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawBounds
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawControl (Reply)
open PV_EVH_LinuxRawHistory (execute Call)
open PV_EVH_World (World)

/-- Every issued request is a suffix of the original source array. This does
not invent an address or assert that numeric addresses implement provenance. -/
def Suffix (base : Nat) (c : Call) : Prop :=
  base ≤ c.address ∧ c.address ≤ base+64 ∧ c.address+c.length = base+64

theorem requests (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel offset : Nat) (a : Array U8 64#usize) (w : World)
    (ho : offset ≤ 64) :
    ∀ c ∈ (execute syscall address fuel offset a w).calls, Suffix address c := by
  induction fuel generalizing offset a w with
  | zero => simp only [execute,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ fuel ih =>
    intro c hc
    simp only [execute,List.mem_cons] at hc
    rcases hc with hc | hc
    · subst c
      simp only [Suffix]
      omega
    · cases hr : (syscall (address+offset) (64-offset) a w).result with
      | fault e => simp only [hr,List.not_mem_nil] at hc
      | exhausted => simp only [hr,List.not_mem_nil] at hc
      | returned r =>
        cases r with
        | fail e => simp only [hr,List.not_mem_nil] at hc
        | div => simp only [hr,List.not_mem_nil] at hc
        | ok ret =>
          simp only [hr] at hc
          split at hc
          next hnonneg =>
            split at hc
            next hz => simp only [List.not_mem_nil] at hc
            next hnz =>
              split at hc
              next hfit =>
                split at hc
                next hend => simp only [List.not_mem_nil] at hc
                next hmore => exact ih _ _ _ (by omega) c hc
              next hlarge => simp only [List.not_mem_nil] at hc
          next hneg =>
            split at hc
            next hintr => exact ih _ _ _ ho c hc
            next hother =>
              split at hc <;> simp only [List.not_mem_nil] at hc

/-- Every byte in every request lies in the original64 interval, including
EINTR, failures and all exhausted prefixes. No success hypothesis is needed. -/
theorem byte_inside (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel : Nat) (a : Array U8 64#usize) (w : World)
    (c : Call) (hc : c ∈ (execute syscall address fuel 0 a w).calls)
    (i : Nat) (hi : i < c.length) :
    address ≤ c.address+i ∧ c.address+i < address+64 := by
  have h := requests syscall address fuel 0 a w (by omega) c hc
  unfold Suffix at h
  omega

#print axioms requests
#print axioms byte_inside
end PV_EVH_LinuxRawBounds
