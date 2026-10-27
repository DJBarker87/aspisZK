import R1Z.PDict_StoreTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0`. -/
theorem erase_0 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0 (types base F) (selected base F ops) = @ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0 base ops := by
  delta ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0
  all_goals rfl
#print axioms erase_0

/-- Carrier transport candidate for `Shared0T.Insts.CoreConvertAsRef`. -/
theorem erase_1 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @Shared0T.Insts.CoreConvertAsRef (types base F) (selected base F ops) = @Shared0T.Insts.CoreConvertAsRef base ops := by
  delta Shared0T.Insts.CoreConvertAsRef
  all_goals rfl
#print axioms erase_1

/-- Carrier transport candidate for `Slice.Insts.CoreConvertAsRefSlice`. -/
theorem erase_2 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @Slice.Insts.CoreConvertAsRefSlice (types base F) (selected base F ops) = @Slice.Insts.CoreConvertAsRefSlice base ops := by
  delta Slice.Insts.CoreConvertAsRefSlice
  all_goals rfl
#print axioms erase_2

/-- Carrier transport candidate for `alloc.string.String.Insts.CoreConvertAsRefPath`. -/
theorem erase_3 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @alloc.string.String.Insts.CoreConvertAsRefPath (types base F) (selected base F ops) = @alloc.string.String.Insts.CoreConvertAsRefPath base ops := by
  delta alloc.string.String.Insts.CoreConvertAsRefPath
  all_goals rfl
#print axioms erase_3

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.reservation_name`. -/
theorem erase_4 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.reservation_name (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.reservation_name base ops := by
  delta aspis_prover.state_only_entropy.reservation_name
  all_goals rfl
#print axioms erase_4

/-- Carrier transport candidate for `block_buffer.Eager.Insts.CoreDefaultDefault`. -/
theorem erase_5 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @block_buffer.Eager.Insts.CoreDefaultDefault (types base F) (selected base F ops) = @block_buffer.Eager.Insts.CoreDefaultDefault base ops := by
  delta block_buffer.Eager.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_5

/-- Carrier transport candidate for `typenum.bit.B0.Insts.CoreDefaultDefault`. -/
theorem erase_12 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B0.Insts.CoreDefaultDefault (types base F) (selected base F ops) = @typenum.bit.B0.Insts.CoreDefaultDefault base ops := by
  delta typenum.bit.B0.Insts.CoreDefaultDefault
  all_goals rfl
#print axioms erase_12

/-- Carrier transport candidate for `typenum.bit.B0.Insts.CoreCloneClone`. -/
theorem erase_13 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B0.Insts.CoreCloneClone (types base F) (selected base F ops) = @typenum.bit.B0.Insts.CoreCloneClone base ops := by
  delta typenum.bit.B0.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_13

/-- Carrier transport candidate for `typenum.bit.B0.Insts.CoreMarkerCopy`. -/
theorem erase_14 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B0.Insts.CoreMarkerCopy (types base F) (selected base F ops) = @typenum.bit.B0.Insts.CoreMarkerCopy base ops := by
  delta typenum.bit.B0.Insts.CoreMarkerCopy
  try simp only [erase_13]
  all_goals rfl
#print axioms erase_14

/-- Carrier transport candidate for `typenum.bit.B0.Insts.TypenumMarker_traitsBit`. -/
theorem erase_15 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.bit.B0.Insts.TypenumMarker_traitsBit (types base F) (selected base F ops) = @typenum.bit.B0.Insts.TypenumMarker_traitsBit base ops := by
  delta typenum.bit.B0.Insts.TypenumMarker_traitsBit
  try simp only [erase_12, erase_14]
  all_goals rfl
#print axioms erase_15
end R1Z.PDict_Static222
