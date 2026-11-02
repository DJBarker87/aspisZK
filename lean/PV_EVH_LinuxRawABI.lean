import PV_EVH_LinuxRawObserve
set_option autoImplicit false
namespace PV_EVH_LinuxRawABI
open Aeneas Aeneas.Std ProverRwFull

def modulus : Nat := 18446744073709551616
def half : Nat := 9223372036854775808

/-- The adopted x86_64/pointer64 branch, not the x32 syscall table. RCX and
R11 are clobbers, not outputs consumed by fill_inner. Inline-asm preservation
and the actual kernel relation remain P under the existing V370 boundary. -/
structure Inputs where
  rax : Nat
  rdi : Nat
  rsi : Nat
  rdx : Nat

def inputs (address length : Nat) : Inputs := ⟨318,address,length,0⟩

/-- Reinterpret the returned RAX word as signed isize64, never Nat truncation
of a negative raw error. The bounded-word premise is the register invariant. -/
def signed (word : Nat) : Int :=
  if word < half then (word : Int) else (word : Int)-(modulus : Int)

def word (ret : Int) : Nat :=
  if ret < 0 then (ret+(modulus : Int)).toNat else ret.toNat

theorem signed_range (n : Nat) (h : n < modulus) :
    -(half : Int) ≤ signed n ∧ signed n < (half : Int) := by
  unfold signed
  split <;> simp only [half,modulus] at * <;> omega

theorem signed_word (ret : Int)
    (lo : -(half : Int) ≤ ret) (hi : ret < (half : Int)) :
    signed (word ret) = ret := by
  unfold signed word
  split <;> split <;> simp only [half,modulus] at * <;> omega

theorem word_range (ret : Int)
    (lo : -(half : Int) ≤ ret) (hi : ret < (half : Int)) :
    word ret < modulus := by
  unfold word
  split <;> simp only [half,modulus] at * <;> omega

/-- All suffix arguments fit the actual 64-bit registers without wrapping,
provided the original64 machine interval is valid. This numeric premise must
come from the actual frame; fresh ghost lifetime keys do not prove it. -/
theorem suffix_inputs (address offset : Nat)
    (ha : address+64 < modulus) (ho : offset ≤ 64) :
    let r := inputs (address+offset) (64-offset)
    r.rax = 318 ∧ r.rdi = address+offset ∧ r.rsi = 64-offset ∧ r.rdx = 0 ∧
    r.rdi < modulus ∧ r.rsi < modulus := by
  dsimp only [inputs]
  refine ⟨rfl,rfl,rfl,rfl,by omega,?_⟩
  unfold modulus
  omega

theorem negative_errno (code : Int) (hc : 0 < code) (hh : code ≤ 4095) :
    signed (word (-code)) = -code ∧ signed (word (-code)) < 0 := by
  have h := signed_word (-code) (by unfold half; omega) (by unfold half; omega)
  exact ⟨h,by rw [h]; omega⟩

#print axioms signed_range
#print axioms signed_word
#print axioms word_range
#print axioms suffix_inputs
#print axioms negative_errno
end PV_EVH_LinuxRawABI
