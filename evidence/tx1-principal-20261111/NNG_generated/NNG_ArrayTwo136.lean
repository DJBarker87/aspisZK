import NNG_Array136
set_option autoImplicit false
namespace AspisR1.NNG_ArrayTwo136
open Aeneas Aeneas.Std NNG_Array136

theorem eta {T : Type} (a : Array T 2#usize) :
 Array.make 2#usize [get a 0#usize (by decide),get a 1#usize (by decide)]=a := by
 rcases a with ⟨xs,size⟩
 cases xs with
 | nil=>cases size
 | cons x xs=>
   cases xs with
   | nil=>cases size
   | cons y xs=>
     cases xs with
     | nil=>rfl
     | cons z xs=>
       have length : (x::y::z::xs).length=2 := size
       simp only [List.length_cons] at length
       omega
#print axioms eta
end AspisR1.NNG_ArrayTwo136
