import NET_InverseRef.Funs
import NEF_FrozenSpecialisation
set_option autoImplicit false
namespace NET_CMReference
open Aeneas Aeneas.Std Result
abbrev C := NEF_FrozenInvRef.field.CM31

def into (x : C) : NET_InverseRef.C := ⟨x.a,x.b⟩
def out (x : NET_InverseRef.C) : C := ⟨x.a,x.b⟩
def ops (inverse : U32 → Result U32) : NET_InverseRef.Base Unit where
 mul := NEF_FrozenInvRef.field.M31.mul
 add := NEF_FrozenInvRef.field.M31.add
 neg := NEF_FrozenInvRef.field.M31.neg
 inv := inverse

/-- Independent safe-Rust reference, actual emitted frozen body, same full
Result. Selecting the backend does not assert that its native bridge is closed. -/
theorem emitted (x : C) (inverse : U32 → Result U32) :
 (do let r ← NET_InverseRef.cm_inverse (ops inverse) (into x); ok (out r)) =
 NEF_FrozenInvRef.field.CM31.inv_with x inverse := by
 simp only [NET_InverseRef.cm_inverse,ops,into,out,
  NEF_FrozenInvRef.field.CM31.inv_with,bind_assoc_eq,bind_tc_ok]

theorem carrier (x : C) : out (into x)=x := by cases x; rfl

/-- The unchanged continuation receives the same nominal CM31 carrier even
when a primitive fails/diverges; errors are not projected away. -/
theorem continuation {R : Type} (x : C) (inverse : U32 → Result U32)
 (k : C → Result R) :
 (do let r ← NET_InverseRef.cm_inverse (ops inverse) (into x); k (out r)) =
 (do let r ← NEF_FrozenInvRef.field.CM31.inv_with x inverse; k r) := by
 have h:=emitted x inverse
 have same:=congrArg (fun z : Result C => z.bind k) h
 simpa only [bind_assoc_eq,bind_tc_ok] using same

#print axioms emitted
#print axioms carrier
#print axioms continuation
end NET_CMReference
