import R1Z.PDict_Static222_00
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `typenum.uint.UInt.Insts.CoreDefaultDefault`. -/
theorem erase_16 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UInt.Insts.CoreDefaultDefault (types base F) (selected base F ops) = @typenum.uint.UInt.Insts.CoreDefaultDefault base ops := by
  delta typenum.uint.UInt.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_16

/-- Carrier transport candidate for `typenum.uint.UInt.Insts.CoreCloneClone`. -/
theorem erase_17 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UInt.Insts.CoreCloneClone (types base F) (selected base F ops) = @typenum.uint.UInt.Insts.CoreCloneClone base ops := by
  delta typenum.uint.UInt.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_17

/-- Carrier transport candidate for `typenum.uint.UInt.Insts.CoreMarkerCopy`. -/
theorem erase_18 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UInt.Insts.CoreMarkerCopy (types base F) (selected base F ops) = @typenum.uint.UInt.Insts.CoreMarkerCopy base ops := by
  delta typenum.uint.UInt.Insts.CoreMarkerCopy
  try simp only [erase_17]
  all_goals rfl
#print axioms erase_18

/-- Carrier transport candidate for `typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned`. -/
theorem erase_19 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned (types base F) (selected base F ops) = @typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned base ops := by
  delta typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned
  try simp only [erase_16, erase_18]
  all_goals rfl
#print axioms erase_19

/-- Carrier transport candidate for `typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven`. -/
theorem erase_20 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven (types base F) (selected base F ops) = @typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven base ops := by
  delta typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven
  try simp only [erase_15, erase_19]
  all_goals rfl
#print axioms erase_20

/-- Carrier transport candidate for `typenum.bit.B1.Insts.CoreDefaultDefault`. -/
theorem erase_21 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B1.Insts.CoreDefaultDefault (types base F) (selected base F ops) = @typenum.bit.B1.Insts.CoreDefaultDefault base ops := by
  delta typenum.bit.B1.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_21

/-- Carrier transport candidate for `typenum.bit.B1.Insts.CoreCloneClone`. -/
theorem erase_22 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B1.Insts.CoreCloneClone (types base F) (selected base F ops) = @typenum.bit.B1.Insts.CoreCloneClone base ops := by
  delta typenum.bit.B1.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_22

/-- Carrier transport candidate for `typenum.bit.B1.Insts.CoreMarkerCopy`. -/
theorem erase_23 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B1.Insts.CoreMarkerCopy (types base F) (selected base F ops) = @typenum.bit.B1.Insts.CoreMarkerCopy base ops := by
  delta typenum.bit.B1.Insts.CoreMarkerCopy
  try simp only [erase_22]
  all_goals rfl
#print axioms erase_23

/-- Carrier transport candidate for `typenum.bit.B1.Insts.TypenumMarker_traitsBit`. -/
theorem erase_24 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B1.Insts.TypenumMarker_traitsBit (types base F) (selected base F ops) = @typenum.bit.B1.Insts.TypenumMarker_traitsBit base ops := by
  delta typenum.bit.B1.Insts.TypenumMarker_traitsBit
  try simp only [erase_21, erase_23]
  all_goals rfl
#print axioms erase_24

/-- Carrier transport candidate for `typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd`. -/
theorem erase_25 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd (types base F) (selected base F ops) = @typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd base ops := by
  delta typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd
  try simp only [erase_24, erase_19]
  all_goals rfl
#print axioms erase_25

/-- Carrier transport candidate for `typenum.uint.UTerm.Insts.CoreDefaultDefault`. -/
theorem erase_26 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UTerm.Insts.CoreDefaultDefault (types base F) (selected base F ops) = @typenum.uint.UTerm.Insts.CoreDefaultDefault base ops := by
  delta typenum.uint.UTerm.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_26

/-- Carrier transport candidate for `typenum.uint.UTerm.Insts.CoreCloneClone`. -/
theorem erase_27 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UTerm.Insts.CoreCloneClone (types base F) (selected base F ops) = @typenum.uint.UTerm.Insts.CoreCloneClone base ops := by
  delta typenum.uint.UTerm.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_27

/-- Carrier transport candidate for `typenum.uint.UTerm.Insts.CoreMarkerCopy`. -/
theorem erase_28 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UTerm.Insts.CoreMarkerCopy (types base F) (selected base F ops) = @typenum.uint.UTerm.Insts.CoreMarkerCopy base ops := by
  delta typenum.uint.UTerm.Insts.CoreMarkerCopy
  try simp only [erase_27]
  all_goals rfl
#print axioms erase_28

/-- Carrier transport candidate for `typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned`. -/
theorem erase_29 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned (types base F) (selected base F ops) = @typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned base ops := by
  delta typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned
  try simp only [erase_26, erase_28]
  all_goals rfl
#print axioms erase_29

/-- Carrier transport candidate for `typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0`. -/
theorem erase_30 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0 (types base F) (selected base F ops) = @typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0 base ops := by
  delta typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0
  try simp only [erase_29]
  all_goals rfl
#print axioms erase_30

end R1Z.PDict_Static222
