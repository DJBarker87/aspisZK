import KMX_CopyMeaning
import NCI_KMXFrames
set_option autoImplicit false
namespace PCB_AppendFrame

def base (filled row : Nat) := 64 + 32 * (filled + row)
def step {α : Type} (roots : Nat → Nat → α) (dst : Nat → α)
    (filled row : Nat) : Nat → α :=
  KMX_CopyMeaning.loop (fun k => roots row (k - base filled row)) dst
    (base filled row) 32

def run {α : Type} (roots : Nat → Nat → α) (dst : Nat → α)
    (filled : Nat) : Nat → Nat → α
  | 0 => dst
  | n+1 => step roots (run roots dst filled n) filled n

theorem geometry (filled offset count : Nat) (cap : filled + count ≤ 256)
    (inside : offset < count) :
    base filled offset + 32 ≤ 8256 ∧ 64 ≤ base filled offset := by
  simp only [base]
  omega

theorem step_byte {α : Type} (roots : Nat → Nat → α) (dst : Nat → α)
    (filled row byte : Nat) (small : byte < 32) :
    step roots dst filled row (base filled row + byte) = roots row byte := by
  unfold step
  rw [KMX_CopyMeaning.loop_spec]
  have h : base filled row ≤ base filled row + byte ∧
      base filled row + byte < base filled row + 32 := by omega
  simp [h]

theorem step_frame {α : Type} (roots : Nat → Nat → α) (dst : Nat → α)
    (filled row k : Nat) (outside : k < base filled row ∨ base filled row + 32 ≤ k) :
    step roots dst filled row k = dst k :=
  KMX_CopyMeaning.copy_frame _ _ _ _ _ outside

theorem retained {α : Type} (roots : Nat → Nat → α) (dst : Nat → α)
    (filled count row byte : Nat) (inside : row < count) (small : byte < 32) :
    run roots dst filled count (base filled row + byte) = roots row byte := by
  induction count with
  | zero => omega
  | succ n ih =>
    simp only [run]
    by_cases last : row = n
    · subst row
      exact step_byte roots _ filled n byte small
    · rw [step_frame]
      · exact ih (by omega)
      · left
        simp only [base]
        omega

theorem run_frame {α : Type} (roots : Nat → Nat → α) (dst : Nat → α)
    (filled count k : Nat)
    (outside : k < base filled 0 ∨ base filled count ≤ k) :
    run roots dst filled count k = dst k := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [step_frame]
    · apply ih
      simp only [base] at *
      omega
    · simp only [base] at *
      omega

def finish {α : Type} (filledBytes dst : Nat → α) : Nat → α :=
  KMX_CopyMeaning.loop filledBytes dst 56 2

theorem finish_roots {α : Type} (filledBytes dst : Nat → α) (k : Nat)
    (root_region : 64 ≤ k) : finish filledBytes dst k = dst k := by
  apply KMX_CopyMeaning.copy_frame
  omega

theorem complete_retained {α : Type} (roots : Nat → Nat → α)
    (filledBytes dst : Nat → α) (filled count row byte : Nat)
    (inside : row < count) (small : byte < 32) :
    finish filledBytes (run roots dst filled count) (base filled row + byte) =
      roots row byte := by
  rw [finish_roots]
  · exact retained roots dst filled count row byte inside small
  · simp only [base]
    omega

#print axioms geometry
#print axioms step_byte
#print axioms step_frame
#print axioms retained
#print axioms run_frame
#print axioms finish_roots
#print axioms complete_retained
end PCB_AppendFrame
