import F3N_ProgramCarrier
import RPz7_SdkD_BatchFixed
import Port9OR_Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_BatchCode
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem raw {Hash : Type} (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) (which : Usize) :
    SdkC_BatchSource.code D hash proof p.queries p.roots root which=
      Port9OR_Batch.code Port4B_Install.leaves E hash proof p root which := by
  simp only [SdkC_BatchSource.code,Port9OR_Batch.code,SdkD_BatchFixed.values Port4B_Install.leaves D E]

#print axioms raw
end AspisR1.F3N_BatchCode
end
