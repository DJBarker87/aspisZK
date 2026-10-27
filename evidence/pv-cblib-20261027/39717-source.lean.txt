import R1Z.ProverRwFullTypes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_WordReference
open ProverRwFull
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev Word := host_commitment.Word
abbrev Item := core.result.Result Word aspis_core.r0.Error

/-- Value-level specification of the prepared safe field-copy reference.
This is not an extracted-source or native-equivalence certificate. -/
def copyQ (q : Q) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def copyWord : Word→Word
  | .Base v => .Base ⟨v.val.map id,by simpa only [List.length_map] using v.property⟩
  | .Secure v => .Secure ⟨v.val.map copyQ,by simpa only [List.length_map] using v.property⟩

def copyItem : Item→Item
  | .Ok w => .Ok (copyWord w)
  | .Err e => .Err e

def copyItems (v : alloc.vec.Vec Item) : alloc.vec.Vec Item :=
  ⟨v.val.map copyItem,by simpa only [List.length_map] using v.property⟩
#print axioms copyQ
#print axioms copyWord
#print axioms copyItem
#print axioms copyItems
end R1Z.PV_CBL_WordReference
