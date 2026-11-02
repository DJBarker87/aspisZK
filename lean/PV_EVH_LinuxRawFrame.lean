import PV_EVH_LinuxRawControl
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawFrame
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawControl (Reply loop)
open PV_EVH_World (World)

def Prefix (a b : Array U8 64#usize) (n : Nat) : Prop :=
  ∀ i, i < n → a.val[i]? = b.val[i]?

/-- Local memory obligation of the raw ABI boundary. This remains P until the
actual syscall memory specification is associated; density does not imply it.
It includes faults and exhaustion, and allows arbitrary writes in the suffix. -/
def KernelFrame (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address : Nat) : Prop :=
  ∀ offset, offset ≤ 64 → ∀ a w,
    Prefix (syscall (address+offset) (64-offset) a w).buffer a offset

/-- Source control cannot overwrite a consumed prefix once each individual
syscall respects its supplied mutable suffix. No uniform successful run or
output distribution is required. -/
theorem consumed_prefix (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address : Nat) (hk : KernelFrame syscall address)
    (fuel offset : Nat) (a : Array U8 64#usize) (w : World) (ho : offset ≤ 64) :
    Prefix (loop syscall address fuel offset a w).buffer a offset := by
  induction fuel generalizing offset a w with
  | zero => intro i hi; rfl
  | succ fuel ih =>
    have hlocal := hk offset ho a w
    simp only [loop]
    cases hr : (syscall (address+offset) (64-offset) a w).result with
    | fault e => simp only [hr]; exact hlocal
    | exhausted => simp only [hr]; exact hlocal
    | returned r =>
      cases r with
      | fail e => simp only [hr]; exact hlocal
      | div => simp only [hr]; exact hlocal
      | ok ret =>
        simp only [hr]
        split
        next hnonneg =>
          split
          next hz => exact hlocal
          next hnz =>
            split
            next hfit =>
              split
              next hend => exact hlocal
              next hmore =>
                have htail := ih (offset+ret.toNat) _ _ (by omega)
                intro i hi
                exact (htail i (by omega)).trans (hlocal i hi)
            next hlarge => exact hlocal
        next hneg =>
          split
          next hintr =>
            have htail := ih offset _ _ ho
            intro i hi
            exact (htail i hi).trans (hlocal i hi)
          next hother => split <;> exact hlocal

#print axioms consumed_prefix
end PV_EVH_LinuxRawFrame
