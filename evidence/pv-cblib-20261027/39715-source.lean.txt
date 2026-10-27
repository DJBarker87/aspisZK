import R1Z.PV_CBL_BufferReference
namespace R1Z.PV_CBL_BufferInvariants
open PV_CBL_LibraryShapes
set_option autoImplicit false

def eager {A : Type} (size : Nat) (v : Buffer A) : Prop := v.pos.val<size

def lazy {A : Type} (size : Nat) (v : Buffer A) : Prop := v.pos.val≤size

theorem eager_implies_lazy {A : Type} (size : Nat) (v : Buffer A) (h : eager size v) :
    lazy size v := Nat.le_of_lt h

theorem initial_eager {A : Type} (size : Nat) (a : A) (h : 0<size) :
    eager size (PV_CBL_BufferReference.initial a) := h

theorem initial_lazy {A : Type} (size : Nat) (a : A) :
    lazy size (PV_CBL_BufferReference.initial a) := Nat.zero_le size

#print axioms eager
#print axioms lazy
#print axioms eager_implies_lazy
#print axioms initial_eager
#print axioms initial_lazy
end R1Z.PV_CBL_BufferInvariants
