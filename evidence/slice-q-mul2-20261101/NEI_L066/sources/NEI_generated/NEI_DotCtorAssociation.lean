import NEI_DotCtorRaw.Funs
import NEI_DotConstructors
set_option autoImplicit false
namespace NEI_DotCtorAssociation
open Aeneas Aeneas.Std Result
abbrev RD := NEI_DotCtorRaw.fast_pairing.canonical.Dot
abbrev RE := NEI_DotCtorRaw.fast_pairing.EbyKDot
abbrev D := NEI_DotConstructors.D
abbrev E := NEI_DotConstructors.E

def toD (x : RD) : D := ⟨x.sums⟩
def fromD (x : D) : RD := ⟨x.sums⟩
def toE (x : RE) : E := ⟨toD x.c0,toD x.c1,x.count⟩
def fromE (x : E) : RE := ⟨fromD x.c0,fromD x.c1,x.count⟩
theorem fromtoD (x : RD) : fromD (toD x)=x := by cases x; rfl
theorem tofromD (x : D) : toD (fromD x)=x := by cases x; rfl
theorem fromtoE (x : RE) : fromE (toE x)=x := by cases x; rfl
theorem tofromE (x : E) : toE (fromE x)=x := by cases x; rfl

theorem emitted_dot :
 (do let x ← NEI_DotCtorRaw.fast_pairing.canonical.Dot.new;ok (toD x))=
 FIo_Native.fast_pairing.canonical.Dot.new := by rfl

theorem emitted_eby :
 (do let x ← NEI_DotCtorRaw.fast_pairing.EbyKDot.new;ok (toE x))=
 FIo_Native.fast_pairing.EbyKDot.new := by rfl

/-- Aggregate arbitrary native observation windows into the entire value. -/
theorem array_zero (sums : Array U64 4#usize)
 (windows : ∀ (j : Nat) (bound : j<4),
   sums.val[j]'(by rw [sums.property];exact bound)=0#u64) :
 sums=Array.repeat 4#usize 0#u64 := by
 cases sums with
 | mk values length =>
  have len : values.length=4 := length
  have all : values=List.replicate 4 0#u64 := by
   apply List.ext_getElem
   · simp only [len,List.length_replicate]
   · intro j valid expected
     simp only [List.getElem_replicate]
     exact windows j (by omega)
  subst values
  rfl

theorem dot_windows (value : D)
 (windows : ∀ (j : Nat) (bound : j<4),
   value.sums.val[j]'(by rw [value.sums.property];exact bound)=0#u64) :
 value=NEI_DotConstructors.zero := by
 have words := array_zero value.sums windows
 cases value
 change (⟨_⟩ : D)=⟨Array.repeat 4#usize 0#u64⟩
 rw [words]

theorem eby_windows (value : E)
 (left : ∀ (j : Nat) (bound : j<4),
   value.c0.sums.val[j]'(by rw [value.c0.sums.property];exact bound)=0#u64)
 (right : ∀ (j : Nat) (bound : j<4),
   value.c1.sums.val[j]'(by rw [value.c1.sums.property];exact bound)=0#u64)
 (count : value.count=0#usize) : value=NEI_DotConstructors.initial := by
 have l := dot_windows value.c0 left
 have r := dot_windows value.c1 right
 cases value
 change (⟨_,_,_⟩ : E)=⟨NEI_DotConstructors.zero,NEI_DotConstructors.zero,0#usize⟩
 rw [l,r,count]
#print axioms fromtoD
#print axioms tofromD
#print axioms fromtoE
#print axioms tofromE
#print axioms emitted_dot
#print axioms emitted_eby
#print axioms array_zero
#print axioms dot_windows
#print axioms eby_windows
end NEI_DotCtorAssociation
