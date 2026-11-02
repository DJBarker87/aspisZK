import PV_EVH_LinuxRawControl
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawCodes
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawControl (Reply Delivery unexpected)
open PV_EVH_World (World)

/-- Exact reached values of deployed Error(NonZeroI32): UNEXPECTED or a signed
negative OS return representable by i32. No fabricated zero error is admitted. -/
def ValidCode (code : Int) : Prop :=
  code = unexpected ∨ (-(2147483648 : Int) ≤ code ∧ code < 0)

def Valid (d : Delivery) : Prop :=
  ∀ code, d.status = .returned (.ok (.Err code)) → ValidCode code

theorem all_codes (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel offset : Nat) (a : Array U8 64#usize) (w : World) :
    Valid (PV_EVH_LinuxRawControl.loop syscall address fuel offset a w) := by
  induction fuel generalizing offset a w with
  | zero =>
    intro code h
    simp only [PV_EVH_LinuxRawControl.loop] at h
    cases h
  | succ fuel ih =>
    intro code h
    simp only [PV_EVH_LinuxRawControl.loop] at h
    cases hr : (syscall (address+offset) (64-offset) a w).result with
    | fault e => simp only [hr] at h; cases h
    | exhausted => simp only [hr] at h; cases h
    | returned r =>
      cases r with
      | fail e => simp only [hr] at h; cases h
      | div => simp only [hr] at h; cases h
      | ok ret =>
        simp only [hr] at h
        split at h
        next hnonneg =>
          split at h
          next hz => cases h; exact Or.inl rfl
          next hnz =>
            split at h
            next hfit =>
              split at h
              next hend => cases h
              next hmore => exact ih _ _ _ code h
            next hlarge => cases h; exact Or.inl rfl
        next hneg =>
          split at h
          next hintr => exact ih _ _ _ code h
          next hother =>
            split at h
            next hfit => cases h; exact Or.inr ⟨hfit,by omega⟩
            next hlarge => cases h; exact Or.inl rfl

theorem nonzero (code : Int) (h : ValidCode code) : code ≠ 0 := by
  rcases h with h | h
  · rw [h]; unfold unexpected; omega
  · omega

#print axioms all_codes
#print axioms nonzero
end PV_EVH_LinuxRawCodes
