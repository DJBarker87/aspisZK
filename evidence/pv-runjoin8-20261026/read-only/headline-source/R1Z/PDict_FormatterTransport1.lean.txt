import R1Z.PDict_FormatterTransport0
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterTransport
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps

theorem lower_12 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B0.Insts.CoreDefaultDefault (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.bit.B0.Insts.CoreDefaultDefault base ops := by
  delta typenum.bit.B0.Insts.CoreDefaultDefault
  rfl
#print axioms lower_12

theorem lower_13 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B0.Insts.CoreCloneClone (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.bit.B0.Insts.CoreCloneClone base ops := by
  delta typenum.bit.B0.Insts.CoreCloneClone
  rfl
#print axioms lower_13

theorem lower_14 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B0.Insts.CoreMarkerCopy (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.bit.B0.Insts.CoreMarkerCopy base ops := by
  delta typenum.bit.B0.Insts.CoreMarkerCopy
  rfl
#print axioms lower_14

theorem lower_15 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B0.Insts.TypenumMarker_traitsBit (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.bit.B0.Insts.TypenumMarker_traitsBit base ops := by
  delta typenum.bit.B0.Insts.TypenumMarker_traitsBit
  rfl
#print axioms lower_15

theorem lower_16 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UInt.Insts.CoreDefaultDefault (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.uint.UInt.Insts.CoreDefaultDefault base ops := by
  delta typenum.uint.UInt.Insts.CoreDefaultDefault
  rfl
#print axioms lower_16

theorem lower_17 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UInt.Insts.CoreCloneClone (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.uint.UInt.Insts.CoreCloneClone base ops := by
  delta typenum.uint.UInt.Insts.CoreCloneClone
  rfl
#print axioms lower_17

theorem lower_18 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UInt.Insts.CoreMarkerCopy (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.uint.UInt.Insts.CoreMarkerCopy base ops := by
  delta typenum.uint.UInt.Insts.CoreMarkerCopy
  rfl
#print axioms lower_18

theorem lower_19 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned base ops := by
  delta typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned
  rfl
#print axioms lower_19

theorem lower_20 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven base ops := by
  delta typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven
  rfl
#print axioms lower_20

theorem lower_21 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B1.Insts.CoreDefaultDefault (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.bit.B1.Insts.CoreDefaultDefault base ops := by
  delta typenum.bit.B1.Insts.CoreDefaultDefault
  rfl
#print axioms lower_21

theorem lower_22 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B1.Insts.CoreCloneClone (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.bit.B1.Insts.CoreCloneClone base ops := by
  delta typenum.bit.B1.Insts.CoreCloneClone
  rfl
#print axioms lower_22

theorem lower_23 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B1.Insts.CoreMarkerCopy (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.bit.B1.Insts.CoreMarkerCopy base ops := by
  delta typenum.bit.B1.Insts.CoreMarkerCopy
  rfl
#print axioms lower_23

theorem lower_24 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B1.Insts.TypenumMarker_traitsBit (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.bit.B1.Insts.TypenumMarker_traitsBit base ops := by
  delta typenum.bit.B1.Insts.TypenumMarker_traitsBit
  rfl
#print axioms lower_24

theorem lower_25 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd (types base F) (PDict_FormatterDictionaryMap.selected base F ops) =
    @typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd base ops := by
  delta typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd
  rfl
#print axioms lower_25
end R1Z.PDict_FormatterTransport
