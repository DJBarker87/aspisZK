import SCH_SdkPure
set_option autoImplicit false
namespace AspisR1.SCH_DigestAlign

theorem source {F C : Type} (c : DrvC_Installation.Configuration F C) :
    DrvC_Installation.digest c = AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std) := rfl

#print axioms source
end AspisR1.SCH_DigestAlign
