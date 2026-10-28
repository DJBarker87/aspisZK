import R1Z.PDict_DigestDelegates
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Array32
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_Publication.native
section Source
def flatten {T : Type}
    (value :
      (PDict_CryptoTypes.generic_array.GenericArray T (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt
        (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt
        typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        (PDict_CryptoTypes.generic_array.GenericArrayImplEven T (PDict_CryptoTypes.generic_array.GenericArrayImplEven T
        (PDict_CryptoTypes.generic_array.GenericArrayImplEven T (PDict_CryptoTypes.generic_array.GenericArrayImplEven T
        (PDict_CryptoTypes.generic_array.GenericArrayImplEven T (PDict_CryptoTypes.generic_array.GenericArrayImplOdd T
        (Array T 0#usize)))))))) ) : Array T 32#usize :=
  Array.make 32#usize [
    value.data.parent1.parent1.parent1.parent1.parent1.data,
    value.data.parent1.parent1.parent1.parent1.parent2.data,
    value.data.parent1.parent1.parent1.parent2.parent1.data,
    value.data.parent1.parent1.parent1.parent2.parent2.data,
    value.data.parent1.parent1.parent2.parent1.parent1.data,
    value.data.parent1.parent1.parent2.parent1.parent2.data,
    value.data.parent1.parent1.parent2.parent2.parent1.data,
    value.data.parent1.parent1.parent2.parent2.parent2.data,
    value.data.parent1.parent2.parent1.parent1.parent1.data,
    value.data.parent1.parent2.parent1.parent1.parent2.data,
    value.data.parent1.parent2.parent1.parent2.parent1.data,
    value.data.parent1.parent2.parent1.parent2.parent2.data,
    value.data.parent1.parent2.parent2.parent1.parent1.data,
    value.data.parent1.parent2.parent2.parent1.parent2.data,
    value.data.parent1.parent2.parent2.parent2.parent1.data,
    value.data.parent1.parent2.parent2.parent2.parent2.data,
    value.data.parent2.parent1.parent1.parent1.parent1.data,
    value.data.parent2.parent1.parent1.parent1.parent2.data,
    value.data.parent2.parent1.parent1.parent2.parent1.data,
    value.data.parent2.parent1.parent1.parent2.parent2.data,
    value.data.parent2.parent1.parent2.parent1.parent1.data,
    value.data.parent2.parent1.parent2.parent1.parent2.data,
    value.data.parent2.parent1.parent2.parent2.parent1.data,
    value.data.parent2.parent1.parent2.parent2.parent2.data,
    value.data.parent2.parent2.parent1.parent1.parent1.data,
    value.data.parent2.parent2.parent1.parent1.parent2.data,
    value.data.parent2.parent2.parent1.parent2.parent1.data,
    value.data.parent2.parent2.parent1.parent2.parent2.data,
    value.data.parent2.parent2.parent2.parent1.parent1.data,
    value.data.parent2.parent2.parent2.parent1.parent2.data,
    value.data.parent2.parent2.parent2.parent2.parent1.data,
    value.data.parent2.parent2.parent2.parent2.parent2.data
  ]
end Source

@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_DigestDelegates.selected base ops with op211 := fun value => .ok (flatten value) }

theorem op211_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op211 (native base) (selected base ops) =
      fun {T : Type} value => .ok (flatten (T := T) value) := rfl

#print axioms op211_installed
end R1Z.PDict_Array32
