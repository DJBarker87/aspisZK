import NNQ_RawChild
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result

theorem raw_sdk_withDigest {F C : Type} (c : DrvC_Installation.Configuration F C)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize)) :
    GExp_SecondPair.sdk (withDigest c o).adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std =
    {GExp_SecondPair.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std with op43 := o} := rfl
#print axioms raw_sdk_withDigest
attribute [local irreducible] GExp_SecondPair.sdk GExq_ChildCode.execute S2W_Outer.stage1_owned S2W_Outer.stage2_owned

theorem caller_first_eq {F C : Type} (c : DrvC_Installation.Configuration F C)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (hv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (id : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) :
    GExq_Caller.first (withDigest c o).adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std hv id accounts data =
    GExq_Caller.first c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std hv id accounts data := by
  unfold GExq_Caller.first
  simp only [GExq_Caller.sdk, raw_sdk_withDigest]
  exact lowerN_sim _ _ (fun x y h => child_raw_sim c o hv x y h)
    (stage1_sim _ o id accounts data)

theorem caller_second_eq {F C : Type} (c : DrvC_Installation.Configuration F C)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (hv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (id : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    GExq_Caller.second (withDigest c o).adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std hv id accounts data slot =
    GExq_Caller.second c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std hv id accounts data slot := by
  unfold GExq_Caller.second
  simp only [GExq_Caller.sdk, raw_sdk_withDigest]
  exact lowerN_sim _ _ (fun x y h => child_raw_sim c o hv x y h)
    (stage2_sim _ o id accounts data slot)
#print axioms caller_first_eq
#print axioms caller_second_eq
end AspisR1.NNQ_HostDigest
end
