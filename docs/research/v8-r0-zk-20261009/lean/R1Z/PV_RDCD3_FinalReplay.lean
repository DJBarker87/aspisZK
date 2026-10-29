import R1Z.PV_RDCD3_FinalAudit
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_FinalReplay
open Aeneas Aeneas.Std Result PV_AL_CircleOwned
/-- Final frozen-cohort replay of both complete V260 operation statements. -/
theorem v260 :
    (∀ (w : PV_B2_253c1.host_weights.Weights) (kind j : Usize),
      PV_B2_253c1.host_weights.Weights.raw w kind j =
        PV_RDCD3_V260Exact.original w kind j) ∧
    (∀ (w : PV_B2_251c1.host_weights.Weights) (kind j : Usize),
      PV_B2_251c1.host_weights.raw_value w kind j =
        PV_RDCD3_V260C_Exact.original w kind j) :=
  PV_RDCD3_V260Complete.complete
/-- Static inverse backend and circle control; no pointer Kani is consumed. -/
theorem v265 :
    (∀ x, aspis_core.field.M31.inv x = PV_RDCD3_V265Inverse.inverse x) ∧
    (∀ (block : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow),
      PV_AL_CircleNative.nativeCircle block row = circle_owned block row) :=
  PV_RDCD3_V265.complete
abbrev MaskQ := ProverRwFull.aspis_core.field.QM31
/-- All selected-mask inputs, complete Result, no new domain hypothesis. -/
theorem v217 (c1 : Array MaskQ 16#usize) (mask : Array MaskQ 10#usize)
    (g : MaskQ) (point : Array MaskQ 10#usize) :
    PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value c1 mask g point =
      PV_RDCD3_CB_OwnedMask.owned.mask c1 mask g point :=
  PV_RDCD3_V217.complete c1 mask g point
#print axioms v260
#print axioms v265
#print axioms v217
end R1Z.PV_RDCD3_FinalReplay
