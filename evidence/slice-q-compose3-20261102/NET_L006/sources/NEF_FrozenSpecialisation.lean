import NEF_FrozenInvRef.Funs
import NEF_EmittedBackend
set_option autoImplicit false
namespace NEF_FrozenSpecialisation
open Aeneas Aeneas.Std Result
abbrev Frozen := NEF_FrozenInvRef.field.CM31

def ops (baseInv : U32 → Result U32) : NEF_BackendRef.Ops Unit where
  mul := NEF_FrozenInvRef.field.M31.mul
  add := NEF_FrozenInvRef.field.M31.add
  neg := NEF_FrozenInvRef.field.M31.neg
  inv := baseInv

def toReference (x : Frozen) : NEF_BackendRef.CM := ⟨x.a,x.b⟩
def fromReference (x : NEF_BackendRef.CM) : Frozen := ⟨x.a,x.b⟩
def direct (baseInv : U32 → Result U32) (x : Frozen) : Result Frozen := do
  let r ← NEF_BackendRef.inv_static_ref (ops baseInv) (toReference x)
  ok (fromReference r)

/-- Actual frozen inv_with extraction, with its REAL arithmetic, overflow,
underflow and backend failures, equals the pointer-free direct reference.
The backend is universally quantified; selecting M31::inv needs no pointer test. -/
theorem frozen_source_specialisation (baseInv : U32 → Result U32) (x : Frozen) :
    NEF_FrozenInvRef.field.CM31.inv_with x baseInv = direct baseInv x := by
  simp only [NEF_FrozenInvRef.field.CM31.inv_with, direct,
    NEF_BackendRef.inv_static_ref,ops,toReference,fromReference,bind_assoc_eq,bind_tc_ok]

/-- A caller's unchanged successful/error continuation may be arbitrary. -/
theorem contextual {R : Type} (baseInv : U32 → Result U32) (x : Frozen)
    (k : Frozen → Result R) :
    (do let r ← NEF_FrozenInvRef.field.CM31.inv_with x baseInv; k r) =
      (do let r ← direct baseInv x; k r) := by
  rw [frozen_source_specialisation]
#print axioms frozen_source_specialisation
#print axioms contextual
end NEF_FrozenSpecialisation
