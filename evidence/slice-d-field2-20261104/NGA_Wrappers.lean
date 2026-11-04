import NGA_SmallResult
set_option autoImplicit false
namespace NGA_Wrappers
open Aeneas Aeneas.Std Result
open NGA_PreparePairs

def small {n : Usize} (left right : Array Q n) : Result Q :=
 NGA_SmallResult.sourceModel (left.val.zip right.val)
def sum2 (left right : Array Q 2#usize) : Result Q := small left right
def sum3 (left right : Array Q 3#usize) : Result Q := small left right
def sum4 (left right : Array Q 4#usize) : Result Q := small left right

theorem domain {n : Usize} (left right : Array Q n)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 (left.val.zip right.val).length=n.val ∧
 ∀ p∈left.val.zip right.val, Canonical p.1 ∧ Canonical p.2 := by
 refine ⟨by simp [List.length_zip,left.property,right.property],?_⟩
 intro p hp
 have h := List.of_mem_zip hp
 exact ⟨hl p.1 h.1,hr p.2 h.2⟩

theorem source {n : Usize} (left right : Array Q n) (arity : n.val≤4)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 ∃ out, small left right=ok out ∧ Canonical out := by
 obtain ⟨length,canonical⟩ := domain left right hl hr
 obtain ⟨cs,sums,out,_,_,_,_,_,_,hc,ho⟩ := NGA_SmallResult.source (left.val.zip right.val)
   (by rw [length];exact arity) canonical
 exact ⟨out,ho,hc⟩

theorem two (left right : Array Q 2#usize)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 ∃ out, sum2 left right=ok out ∧ Canonical out := source left right (by decide) hl hr

theorem three (left right : Array Q 3#usize)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 ∃ out, sum3 left right=ok out ∧ Canonical out := source left right (by decide) hl hr

theorem four (left right : Array Q 4#usize)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 ∃ out, sum4 left right=ok out ∧ Canonical out := source left right (by decide) hl hr

#print axioms domain
#print axioms source
#print axioms two
#print axioms three
#print axioms four
end NGA_Wrappers
