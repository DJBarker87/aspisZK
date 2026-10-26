import SCH_UpdateValidate
set_option autoImplicit false
namespace AspisR1.SCH_SdkSecond
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
local notation "original" => GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std
local notation "ideal" => SCH_IdealSdk.dictionary c hashv H

theorem validation : AdapterRw.r1_pool_adapter.owned.validate_asq8 ideal =
    AdapterRw.r1_pool_adapter.owned.validate_asq8 original :=
  (congrArg AdapterRw.r1_pool_adapter.owned.validate_asq8 (SCH_ChildUpdate.original c hashv H)).trans
    (SCH_UpdateValidate.same _ _)

theorem range : AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ideal =
    AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice original :=
  (congrArg AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
    (SCH_ChildUpdate.original c hashv H)).trans (SCH_SecondPure.full_range _ _)

theorem option_eq {A : Type} (eq : core.cmp.PartialEq A A) :
    AdapterRw.core.option.Option.Insts.CoreCmpPartialEqOption ideal eq =
      AdapterRw.core.option.Option.Insts.CoreCmpPartialEqOption original eq := rfl

theorem statement_bytes :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ideal =
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES original := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
  rfl

#print axioms validation
#print axioms range
#print axioms option_eq
#print axioms statement_bytes
end AspisR1.SCH_SdkSecond
