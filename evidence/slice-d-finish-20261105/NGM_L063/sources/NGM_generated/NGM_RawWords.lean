import RPz7_FIo_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGM_RawWords
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

def words (x : E) : Array U32 8#usize := Array.make 8#usize
 [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]
def nativeWords (x : FIo_Install.NE) : Array U32 8#usize := Array.make 8#usize
 [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem to_native (x : E) : nativeWords (FIo_Install.toE x)=words x := rfl
theorem from_native (x : FIo_Install.NE) : words (FIo_Install.fromE x)=nativeWords x := rfl

theorem injective : Function.Injective words := by
 intro x y same
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
 rcases y with ⟨⟨⟨i,j⟩,⟨k,l⟩⟩,⟨⟨m,n⟩,⟨o,p⟩⟩⟩
 have values := congrArg (fun a : Array U32 8#usize=>a.val) same
 simp only [words,Array.make,List.cons.injEq,eq_self_iff_true,and_true] at values
 rcases values with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
 rfl

theorem equal (x y : E) : words x=words y ↔ x=y := ⟨fun h=>injective h,fun h=>congrArg words h⟩

theorem array_two {A : Type} (xs : Array A 2#usize) :
 ∃ a b,xs=Array.make 2#usize [a,b] := by
 obtain ⟨values,size⟩ := xs
 have size : values.length=2 := by simpa using size
 rcases values with _ | ⟨a,values⟩
 · simp at size
 rcases values with _ | ⟨b,values⟩
 · simp at size
 have empty : values.length=0 := by simp only [List.length_cons] at size;omega
 cases values with
 | nil => exact ⟨a,b,rfl⟩
 | cons c rest => simp at empty
#print axioms to_native
#print axioms from_native
#print axioms injective
#print axioms equal
#print axioms array_two
end AspisR1.NGM_RawWords
end
