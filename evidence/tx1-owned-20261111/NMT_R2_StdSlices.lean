import NMT_R2_ListEquality
import NMT_345Carriers
set_option autoImplicit false
noncomputable section
namespace NMT_R2_StdSlices
open Aeneas Aeneas.Std NMT_345Std NMT_345

def eq {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U) (xs : Slice T) (ys : Array U N) : Result Bool :=
 if xs.val.length != ys.val.length then .ok false else listEq cmp.eq xs.val ys.val

def ne {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U) (xs : Slice T) (ys : Array U N) : Result Bool := do
 let same ← eq cmp xs ys
 .ok (!same)

theorem byte_eq {N : Usize} (xs : Slice U8) (ys : Array U8 N) :
 eq core.cmp.PartialEqU8 xs ys = .ok (decide (xs.val = ys.val)) := by
 unfold eq
 by_cases h : xs.val.length = ys.val.length
 · simp only [h,bne_self_eq_false,Bool.false_eq_true,if_false]
   exact NMT_R2_ListEquality.source _ _
 · have different : xs.val ≠ ys.val := fun same => h (congrArg List.length same)
   have bad : (xs.val.length != ys.val.length) = true := by
    simp only [bne, Bool.not_eq_true', beq_eq_false_iff_ne]
    exact h
   rw [bad]
   simp only [if_true,different,decide_false]

theorem byte_ne {N : Usize} (xs : Slice U8) (ys : Array U8 N) :
 ne core.cmp.PartialEqU8 xs ys = .ok (decide (xs.val ≠ ys.val)) := by
 unfold ne
 rw [byte_eq]
 by_cases h : xs.val = ys.val <;> simp [h]

def install (c : Calls) : Calls := {c with c0 := @ne,c1 := @eq}
#print axioms byte_eq
#print axioms byte_ne
end NMT_R2_StdSlices
end
