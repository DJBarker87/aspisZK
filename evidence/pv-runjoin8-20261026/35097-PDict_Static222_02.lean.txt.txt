import R1Z.PDict_Static222_01
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `typenum.Equal.Insts.TypenumMarker_traitsOrd`. -/
theorem erase_37 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.Equal.Insts.TypenumMarker_traitsOrd (types base F) (selected base F ops) = @typenum.Equal.Insts.TypenumMarker_traitsOrd base ops := by
  delta typenum.Equal.Insts.TypenumMarker_traitsOrd
  all_goals rfl
#print axioms erase_37

/-- Carrier transport candidate for `typenum.Greater.Insts.TypenumMarker_traitsOrd`. -/
theorem erase_38 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.Greater.Insts.TypenumMarker_traitsOrd (types base F) (selected base F ops) = @typenum.Greater.Insts.TypenumMarker_traitsOrd base ops := by
  delta typenum.Greater.Insts.TypenumMarker_traitsOrd
  all_goals rfl
#print axioms erase_38

/-- Carrier transport candidate for `typenum.private.IsLessPrivateABLessB1.Blanket`. -/
theorem erase_39 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.private.IsLessPrivateABLessB1.Blanket (types base F) (selected base F ops) = @typenum.private.IsLessPrivateABLessB1.Blanket base ops := by
  delta typenum.private.IsLessPrivateABLessB1.Blanket
  try simp only [erase_24]
  all_goals rfl
#print axioms erase_39

/-- Carrier transport candidate for `typenum.type_operators.IsLess.Blanket`. -/
theorem erase_40 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.type_operators.IsLess.Blanket (types base F) (selected base F ops) = @typenum.type_operators.IsLess.Blanket base ops := by
  delta typenum.type_operators.IsLess.Blanket
  all_goals rfl
#print axioms erase_40

/-- Carrier transport candidate for `typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output`. -/
theorem erase_41 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output (types base F) (selected base F ops) = @typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output base ops := by
  delta typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output
  all_goals rfl
#print axioms erase_41

/-- Carrier transport candidate for `typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output`. -/
theorem erase_42 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output (types base F) (selected base F ops) = @typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output base ops := by
  delta typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output
  all_goals rfl
#print axioms erase_42

/-- Carrier transport candidate for `typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output`. -/
theorem erase_43 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output (types base F) (selected base F ops) = @typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output base ops := by
  delta typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output
  all_goals rfl
#print axioms erase_43

/-- Carrier transport candidate for `typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess`. -/
theorem erase_44 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess (types base F) (selected base F ops) = @typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess base ops := by
  delta typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess
  all_goals rfl
#print axioms erase_44

/-- Carrier transport candidate for `typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket`. -/
theorem erase_46 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket (types base F) (selected base F ops) = @typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket base ops := by
  delta typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket
  try simp only [erase_24]
  all_goals rfl
#print axioms erase_46

/-- Carrier transport candidate for `typenum.type_operators.IsLessOrEqual.Blanket`. -/
theorem erase_47 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @typenum.type_operators.IsLessOrEqual.Blanket (types base F) (selected base F ops) = @typenum.type_operators.IsLessOrEqual.Blanket base ops := by
  delta typenum.type_operators.IsLessOrEqual.Blanket
  all_goals rfl
#print axioms erase_47
end R1Z.PDict_Static222
