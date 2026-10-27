import R1Z.PDict_CtUpdate
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_CtConstructor
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_CtUpdate.native
variable (base : ExternalTypes)
/-- Exact extracted constructor, with the existing std unwrap definition
reduced to its two branches, erasing its unused Debug argument. -/
def construct
  {T : Type} {OutSize : Type} (O : Type) {Clause0_Clause0_Clause0_BlockSize :
  Type} {Clause0_Clause0_Clause0_Clause0_ArrayType : Type}
  {Clause0_Clause1_OutputSize : Type} {Clause0_Clause1_Clause0_ArrayType :
  Type} {Clause0_Clause2_BufferKind : Type} {Clause0_Clause2_Clause0_BlockSize
  : Type} {Clause0_Clause2_Clause0_Clause0_ArrayType : Type}
  {Clause0_Clause3_Output : Type} {Clause1_ArrayType : Type} {Clause2_Output :
  Type} {Clause4_Output : Type} (VariableOutputCoreInst :
  @digest.core_api.VariableOutputCore (native base) T Clause0_Clause0_Clause0_BlockSize
  Clause0_Clause0_Clause0_Clause0_ArrayType Clause0_Clause1_OutputSize
  Clause0_Clause1_Clause0_ArrayType Clause0_Clause2_BufferKind
  Clause0_Clause2_Clause0_BlockSize Clause0_Clause2_Clause0_Clause0_ArrayType
  Clause0_Clause3_Output)
  (generic_arrayArrayLengthOutSizeU8Clause1_ArrayTypeInst :
  generic_array.ArrayLength OutSize Std.U8 Clause1_ArrayType)
  (typenumtype_operatorsIsLessOrEqualInst :
  typenum.type_operators.IsLessOrEqual OutSize Clause0_Clause1_OutputSize
  Clause2_Output) (typenummarker_traitsNonZeroInst :
  typenum.marker_traits.NonZero Clause2_Output)
  (typenumtype_operatorsIsLessClause0_Clause0_Clause0_BlockSizeUIntUIntUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0B0B0Clause4_OutputInst
  : typenum.type_operators.IsLess Clause0_Clause0_Clause0_BlockSize
  (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt
  (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt (PDict_UInt.typenum.uint.UInt
  (PDict_UInt.typenum.uint.UInt typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0)
  typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
  typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) Clause4_Output)
  (typenummarker_traitsNonZeroInst1 : typenum.marker_traits.NonZero
  Clause4_Output) :
  Result (PDict_CryptoTypes.digest.core_api.ct_variable.CtVariableCoreWrapper T OutSize O
    Clause0_Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_Clause0_ArrayType
    Clause0_Clause1_OutputSize Clause0_Clause1_Clause0_ArrayType
    Clause0_Clause2_BufferKind Clause0_Clause2_Clause0_BlockSize
    Clause0_Clause2_Clause0_Clause0_ArrayType Clause0_Clause3_Output
    Clause1_ArrayType Clause2_Output Clause4_Output)
  :=
  letI : ExternalTypes := native base
  do
  let i ←
    generic_arrayArrayLengthOutSizeU8Clause1_ArrayTypeInst.typenummarker_traitsUnsignedInst.USIZE
  let r ← VariableOutputCoreInst.new i
  let t ← match r with
    | .Ok value => .ok value
    | .Err _ => .fail .panic
  ok { inner := t, _out := () }

@[reducible] def selected (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_CtUpdate.selected base ops with op218 := construct base }
theorem op218_installed (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op218 (native base) (selected base ops) = @construct base := rfl
#print axioms op218_installed
end R1Z.PDict_CtConstructor
