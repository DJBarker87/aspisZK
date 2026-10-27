import GExq_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_BatchCode
open Aeneas Aeneas.Std Result

/-- Test the literal code carrier rather than inferring logs from erasure. -/
theorem current {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (root : Array U8 32#usize) :
    GExq_BatchSource.current D hash proof p root =
      SdkC_BatchSource.currentCode hashv proof p root := by
  rfl

#print axioms current
end AspisR1.SCG_BatchCode
end
