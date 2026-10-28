import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace ProverRwFull

class ExternalTypes where
  op0 : Type
  op1 : Type
  op2 : Type
  op3 : Type
  op4 : Type
  op5 : Type
  op6 : Type
  op7 : Type
  op8 :
      Type
  op9 (U : Type) (B : Type) : Type
  op10 : Type
  op11 (T : Type) (U : Type) (Clause0_ArrayType :
      Type) : Type
  op12 (T : Type) (U : Type) : Type
  op13 (T : Type) (U : Type) : Type
  op14 (BlockSize : Type) (Kind : Type)
      (Clause0_ArrayType : Type) (Clause1_Output : Type) : Type
  op15 (T : Type) (Clause0_BufferKind :
      Type) (Clause0_Clause0_BlockSize : Type) (Clause0_Clause0_Clause0_ArrayType :
      Type) (Clause1_Output : Type) : Type
  op16 (T : Type) (OutSize :
      Type) (O : Type) (Clause0_Clause0_Clause0_BlockSize : Type)
      (Clause0_Clause0_Clause0_Clause0_ArrayType : Type)
      (Clause0_Clause1_OutputSize : Type) (Clause0_Clause1_Clause0_ArrayType :
      Type) (Clause0_Clause2_BufferKind : Type) (Clause0_Clause2_Clause0_BlockSize
      : Type) (Clause0_Clause2_Clause0_Clause0_ArrayType : Type)
      (Clause0_Clause3_Output : Type) (Clause1_ArrayType : Type) (Clause2_Output :
      Type) (Clause4_Output : Type) : Type
  op17 : Type
  op18 : Type
  op19 : Type
  op20 :
      Type
  op21 : Type
  op22 :
      Type
  op23 :
      Type
  op24 : Type
  op25 : Type
  op26 : Type
  op27 : Type

abbrev std.fs.File [ext : ExternalTypes] := @ExternalTypes.op0 ext
abbrev std.fs.OpenOptions [ext : ExternalTypes] := @ExternalTypes.op1 ext
abbrev std.path.Path [ext : ExternalTypes] := @ExternalTypes.op2 ext
abbrev std.io.error.Error [ext : ExternalTypes] := @ExternalTypes.op3 ext
abbrev std.path.PathBuf [ext : ExternalTypes] := @ExternalTypes.op4 ext
abbrev alloc.collections.TryReserveError [ext : ExternalTypes] := @ExternalTypes.op5 ext
abbrev aspis_core.state_only_prefix.r0.Error [ext : ExternalTypes] := @ExternalTypes.op6 ext
abbrev getrandom.error.Error [ext : ExternalTypes] := @ExternalTypes.op7 ext
abbrev aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 [ext : ExternalTypes] := @ExternalTypes.op8 ext
abbrev typenum.uint.UInt [ext : ExternalTypes] := @ExternalTypes.op9 ext
abbrev sha2.core_api.Sha256VarCore [ext : ExternalTypes] := @ExternalTypes.op10 ext
abbrev generic_array.GenericArray [ext : ExternalTypes] := @ExternalTypes.op11 ext
abbrev generic_array.GenericArrayImplOdd [ext : ExternalTypes] := @ExternalTypes.op12 ext
abbrev generic_array.GenericArrayImplEven [ext : ExternalTypes] := @ExternalTypes.op13 ext
abbrev block_buffer.BlockBuffer [ext : ExternalTypes] := @ExternalTypes.op14 ext
abbrev digest.core_api.wrapper.CoreWrapper [ext : ExternalTypes] := @ExternalTypes.op15 ext
abbrev digest.core_api.ct_variable.CtVariableCoreWrapper [ext : ExternalTypes] := @ExternalTypes.op16 ext
abbrev aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1 [ext : ExternalTypes] := @ExternalTypes.op17 ext
abbrev aspis_statement.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1 [ext : ExternalTypes] := @ExternalTypes.op18 ext
abbrev aspis_statement.pool_v1.pair_trace.PoolV1PairTraceVariantV1 [ext : ExternalTypes] := @ExternalTypes.op19 ext
abbrev aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 [ext : ExternalTypes] := @ExternalTypes.op20 ext
abbrev aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 [ext : ExternalTypes] := @ExternalTypes.op21 ext
abbrev aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 [ext : ExternalTypes] := @ExternalTypes.op22 ext
abbrev aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1 [ext : ExternalTypes] := @ExternalTypes.op23 ext
abbrev aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1 [ext : ExternalTypes] := @ExternalTypes.op24 ext
abbrev weights.Weights [ext : ExternalTypes] := @ExternalTypes.op25 ext
abbrev F64 [ext : ExternalTypes] := @ExternalTypes.op26 ext
abbrev core.fmt.Formatter [ext : ExternalTypes] := @ExternalTypes.op27 ext

structure core.fmt.Debug [ExternalTypes] (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

end ProverRwFull
