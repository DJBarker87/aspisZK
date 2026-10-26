import SCH_SdkPure
set_option autoImplicit false
namespace AspisR1.SCH_DigestAlign
attribute [local irreducible] DrvC_Installation.digest GExq_Caller.sdk

theorem source {F C : Type} (c : DrvC_Installation.Configuration F C) :
    DrvC_Installation.digest c = AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std) := by
  unfold DrvC_Installation.digest GExq_Caller.sdk
  rfl

#print axioms source
end AspisR1.SCH_DigestAlign
