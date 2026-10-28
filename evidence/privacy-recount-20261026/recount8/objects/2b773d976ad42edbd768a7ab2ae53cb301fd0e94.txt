import R1Z.PV_RDB2_Layout
import Aeneas.Std

namespace R1Z.PV_RDB2_LayoutGuards
set_option autoImplicit false
open Aeneas Aeneas.Std Result

structure Layout where
  size : Nat
  align : Nat
  deriving DecidableEq

def maximum (halfWord align : Nat) : Nat := halfWord-align

def oldFrom (halfWord size align : Nat) : Except Unit Layout :=
  if size ≤ maximum halfWord align then .ok ⟨size,align⟩ else .error ()

def deployedFrom (halfWord size align : Nat) : Except Unit Layout :=
  if size > maximum halfWord align then .error () else .ok ⟨size,align⟩

theorem from_size_alignment (halfWord size align : Nat) :
    oldFrom halfWord size align = deployedFrom halfWord size align := by
  by_cases h : size ≤ maximum halfWord align
  · simp only [oldFrom,deployedFrom,h,if_true,show ¬size > maximum halfWord align by omega,if_false]
  · simp only [oldFrom,deployedFrom,h,if_false,show size > maximum halfWord align by omega,if_true]

def oldValid (alignment : Option Nat) (halfWord size : Nat) : Bool :=
  match alignment with
  | none => false
  | some align => decide (size ≤ maximum halfWord align)

def deployedValid (alignment : Option Nat) (halfWord size : Nat) : Bool :=
  match alignment with
  | none => false
  | some align => if size > maximum halfWord align then false else true

theorem is_size_align_valid (alignment : Option Nat) (halfWord size : Nat) :
    oldValid alignment halfWord size = deployedValid alignment halfWord size := by
  cases alignment with
  | none => rfl
  | some align =>
    by_cases h : size ≤ maximum halfWord align
    · simp only [oldValid,deployedValid,h,decide_true,show ¬size > maximum halfWord align by omega,if_false]
    · simp only [oldValid,deployedValid,h,decide_false,show size > maximum halfWord align by omega,if_true]

theorem unchecked_sub_bound (halfWord align : Nat) (h : align ≤ halfWord) :
    maximum halfWord align+align=halfWord := by unfold maximum; omega

theorem summation_guard (halfWord size align : Nat) (ha : 0 < align) (hb : align ≤ halfWord) :
    size ≤ maximum halfWord align ↔ size+align-1 ≤ halfWord-1 := by
  unfold maximum
  omega

/-- Public Layout errors remain values, not panic/divergence, and constructor
validation never changes the allocator world. -/
theorem complete_effect {World : Type} (halfWord size align : Nat) (world : World) :
    (ok (oldFrom halfWord size align,world) : Result (Except Unit Layout × World)) =
      ok (deployedFrom halfWord size align,world) := by rw [from_size_alignment]

#print axioms from_size_alignment
#print axioms is_size_align_valid
#print axioms unchecked_sub_bound
#print axioms summation_guard
#print axioms complete_effect
end R1Z.PV_RDB2_LayoutGuards
