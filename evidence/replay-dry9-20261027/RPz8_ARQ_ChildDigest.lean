import RPz8_ARQ_Installation
set_option autoImplicit false
namespace AspisR1.ARQ_ChildDigest
open DrvC_Installation

/-- Symbolic transport through a dictionary equality. Avoid reducing the
entire two installed dictionaries inside a large source-code conversion. -/
theorem current {F C : Type} (c : Configuration F C)
    (aligned : sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std) :
    currentDigest c = AspisS6CurrentFirstInstallation.toDigest
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
          c.reserved c.query c.geometry c.boundaries c.std)) :=
  congrArg AspisS6CurrentFirstInstallation.toDigest
    (congrArg AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 aligned)

#print axioms current
end AspisR1.ARQ_ChildDigest
