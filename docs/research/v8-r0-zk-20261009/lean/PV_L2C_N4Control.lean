import PV_L2C_NativeBalance
import PV_L2C_PaddingNative
set_option autoImplicit false
namespace PV_L2C_N4Control
open PV_L2C_M31 PV_L2C_NativeQ

def count (sums : List word) : Nat :=
  sums.foldl (fun n sum => if sum = 0 then n+1 else n) 0

theorem fold_count (sums : List word) (h : ∀ s ∈ sums, s = 0) (start : Nat) :
    sums.foldl (fun n sum => if sum = 0 then n+1 else n) start = start+sums.length := by
  induction sums generalizing start with
  | nil => simp
  | cons s rest ih =>
    rw [List.foldl_cons,if_pos (h s (by simp)),ih (by intro v hv;exact h v (by simp [hv]))]
    simp;omega
#print axioms fold_count

theorem counted (sums : List word) (h : ∀ s ∈ sums, s = 0) : count sums = sums.length := by
  simpa only [count,Nat.zero_add] using fold_count sums h 0
#print axioms counted

structure Audit where
  c1Columns : Nat
  maskOnlyColumns : Nat
  dBalanced : Bool
  gBalanced : Bool
  paddingBalanced : Bool
inductive Failure where
  | semantic

def guard (audit : Audit) : Except Failure Unit :=
  if audit.c1Columns ≠ 16 ∨ audit.maskOnlyColumns ≠ 10 ∨
    audit.dBalanced = false ∨ audit.gBalanced = false ∨ audit.paddingBalanced = false
  then .error .semantic else .ok ()

theorem complete (c1 maskOnly : List word) (h1 : c1.length = 16) (h2 : maskOnly.length = 10)
    (hc1 : ∀ s ∈ c1, s = 0) (hc2 : ∀ s ∈ maskOnly, s = 0) :
    guard ⟨count c1,count maskOnly,true,true,true⟩ = .ok () := by
  rw [counted c1 hc1,counted maskOnly hc2,h1,h2]
  rfl
#print axioms complete
end PV_L2C_N4Control
