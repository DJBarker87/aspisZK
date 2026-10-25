import GExq_Caller
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterGoodTwo
open Aeneas Aeneas.Std Result S2W_Trace GExq_OuterLower GExq_OuterGoodLaws

theorem two (sdk : AdapterRw.Ops) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : S2Z.Oracle.NativeBinding sdk hashv)
    (program : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    Good hashv (S2W_Observation.two sdk program accounts1 data1 accounts2 data2 slot) := by
  unfold S2W_Observation.two
  apply bind_good
  · exact GExq_OuterGoodStage1.stage1 sdk hashv law program accounts1 data1
  · intro first
    cases first with
    | Err e => exact pure_good _ _
    | Ok saved =>
      apply bind_good
      · exact GExq_OuterGoodStage2.stage2 sdk hashv law program accounts2 data2 slot
      · intro second
        cases second <;> exact pure_good _ _

#print axioms two
end AspisR1.GExq_OuterGoodTwo
end
