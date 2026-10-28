import NDE_Reference4.Funs
import NDE_LiftBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_ClaimBridge
abbrev Q := FIq_Native.field.QM31

def toRef (q : Q) : NDE_Reference4.Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromRef (q : NDE_Reference4.Q) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def claimsToRef (a : Array Q 84#usize) : Array NDE_Reference4.Q 84#usize :=
  ⟨a.val.map toRef, by simpa using a.property⟩

theorem index_transport (a : Array Q 84#usize) (i : Usize) :
    NDE_LiftBridge.mapResult fromRef (Array.index_usize (claimsToRef a) i) =
    Array.index_usize a i := by
  simp [Array.index_usize, claimsToRef, NDE_LiftBridge.mapResult, fromRef, toRef]

#print axioms index_transport
end NDE_ClaimBridge
