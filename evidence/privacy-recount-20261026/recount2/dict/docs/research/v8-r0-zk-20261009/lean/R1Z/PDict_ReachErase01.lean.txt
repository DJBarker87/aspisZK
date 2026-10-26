import R1Z.PDict_ReachErase00
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `typenum.uint.UInt.Insts.CoreDefaultDefault`. -/
theorem erase_16 (ops other : ExternalFuns) :
    @typenum.uint.UInt.Insts.CoreDefaultDefault _ (replace ops other) = @typenum.uint.UInt.Insts.CoreDefaultDefault _ ops := by
  delta typenum.uint.UInt.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_16

/-- Full symbolic source-function equality for `typenum.uint.UInt.Insts.CoreCloneClone`. -/
theorem erase_17 (ops other : ExternalFuns) :
    @typenum.uint.UInt.Insts.CoreCloneClone _ (replace ops other) = @typenum.uint.UInt.Insts.CoreCloneClone _ ops := by
  delta typenum.uint.UInt.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_17

/-- Full symbolic source-function equality for `typenum.uint.UInt.Insts.CoreMarkerCopy`. -/
theorem erase_18 (ops other : ExternalFuns) :
    @typenum.uint.UInt.Insts.CoreMarkerCopy _ (replace ops other) = @typenum.uint.UInt.Insts.CoreMarkerCopy _ ops := by
  delta typenum.uint.UInt.Insts.CoreMarkerCopy
  try simp only [erase_17]
  all_goals rfl
#print axioms erase_18

/-- Full symbolic source-function equality for `typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned`. -/
theorem erase_19 (ops other : ExternalFuns) :
    @typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned _ (replace ops other) = @typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned _ ops := by
  delta typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned
  try simp only [erase_16, erase_18]
  all_goals rfl
#print axioms erase_19

/-- Full symbolic source-function equality for `typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven`. -/
theorem erase_20 (ops other : ExternalFuns) :
    @typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven _ (replace ops other) = @typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven _ ops := by
  delta typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven
  try simp only [erase_15, erase_19]
  all_goals rfl
#print axioms erase_20

/-- Full symbolic source-function equality for `typenum.bit.B1.Insts.CoreDefaultDefault`. -/
theorem erase_21 (ops other : ExternalFuns) :
    @typenum.bit.B1.Insts.CoreDefaultDefault _ (replace ops other) = @typenum.bit.B1.Insts.CoreDefaultDefault _ ops := by
  delta typenum.bit.B1.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_21

/-- Full symbolic source-function equality for `typenum.bit.B1.Insts.CoreCloneClone`. -/
theorem erase_22 (ops other : ExternalFuns) :
    @typenum.bit.B1.Insts.CoreCloneClone _ (replace ops other) = @typenum.bit.B1.Insts.CoreCloneClone _ ops := by
  delta typenum.bit.B1.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_22

/-- Full symbolic source-function equality for `typenum.bit.B1.Insts.CoreMarkerCopy`. -/
theorem erase_23 (ops other : ExternalFuns) :
    @typenum.bit.B1.Insts.CoreMarkerCopy _ (replace ops other) = @typenum.bit.B1.Insts.CoreMarkerCopy _ ops := by
  delta typenum.bit.B1.Insts.CoreMarkerCopy
  try simp only [erase_22]
  all_goals rfl
#print axioms erase_23

/-- Full symbolic source-function equality for `typenum.bit.B1.Insts.TypenumMarker_traitsBit`. -/
theorem erase_24 (ops other : ExternalFuns) :
    @typenum.bit.B1.Insts.TypenumMarker_traitsBit _ (replace ops other) = @typenum.bit.B1.Insts.TypenumMarker_traitsBit _ ops := by
  delta typenum.bit.B1.Insts.TypenumMarker_traitsBit
  try simp only [erase_21, erase_23]
  all_goals rfl
#print axioms erase_24

/-- Full symbolic source-function equality for `typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd`. -/
theorem erase_25 (ops other : ExternalFuns) :
    @typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd _ (replace ops other) = @typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd _ ops := by
  delta typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd
  try simp only [erase_24, erase_19]
  all_goals rfl
#print axioms erase_25

/-- Full symbolic source-function equality for `typenum.uint.UTerm.Insts.CoreDefaultDefault`. -/
theorem erase_26 (ops other : ExternalFuns) :
    @typenum.uint.UTerm.Insts.CoreDefaultDefault _ (replace ops other) = @typenum.uint.UTerm.Insts.CoreDefaultDefault _ ops := by
  delta typenum.uint.UTerm.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_26

/-- Full symbolic source-function equality for `typenum.uint.UTerm.Insts.CoreCloneClone`. -/
theorem erase_27 (ops other : ExternalFuns) :
    @typenum.uint.UTerm.Insts.CoreCloneClone _ (replace ops other) = @typenum.uint.UTerm.Insts.CoreCloneClone _ ops := by
  delta typenum.uint.UTerm.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_27

/-- Full symbolic source-function equality for `typenum.uint.UTerm.Insts.CoreMarkerCopy`. -/
theorem erase_28 (ops other : ExternalFuns) :
    @typenum.uint.UTerm.Insts.CoreMarkerCopy _ (replace ops other) = @typenum.uint.UTerm.Insts.CoreMarkerCopy _ ops := by
  delta typenum.uint.UTerm.Insts.CoreMarkerCopy
  try simp only [erase_27]
  all_goals rfl
#print axioms erase_28

/-- Full symbolic source-function equality for `typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned`. -/
theorem erase_29 (ops other : ExternalFuns) :
    @typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned _ (replace ops other) = @typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned _ ops := by
  delta typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned
  try simp only [erase_26, erase_28]
  all_goals rfl
#print axioms erase_29

/-- Full symbolic source-function equality for `typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0`. -/
theorem erase_30 (ops other : ExternalFuns) :
    @typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0 _ (replace ops other) = @typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0 _ ops := by
  delta typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0
  try simp only [erase_29]
  all_goals rfl
#print axioms erase_30

/-- Full symbolic source-function equality for `sha2.core_api.Sha256VarCore.Insts.Crypto_commonOutputSizeUserUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80`. -/
theorem erase_31 (ops other : ExternalFuns) :
    @sha2.core_api.Sha256VarCore.Insts.Crypto_commonOutputSizeUserUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80 _ (replace ops other) = @sha2.core_api.Sha256VarCore.Insts.Crypto_commonOutputSizeUserUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80 _ ops := by
  delta sha2.core_api.Sha256VarCore.Insts.Crypto_commonOutputSizeUserUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80
  try simp only [erase_20, erase_25, erase_30]
  all_goals rfl
#print axioms erase_31
end R1Z.PDict_ReachErase
