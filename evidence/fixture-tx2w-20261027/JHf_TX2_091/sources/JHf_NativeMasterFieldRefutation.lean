import JHf_MasterFieldRefutation
import JHf_NativeRefutation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_NativeMasterFieldRefutation
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (slot : S2W_ExtractionBoundary.Slot)
    (field : JHf_AuthenticationInstalledDomain.Field (sdk (JHf_ReconstructionConfiguration.value c err))) :
    JHf_NativeRefutation.native c err CPH_Program.verifier (JHb_World.e2.second secondSizes)
      JHb_DataRequest.value slot≠ok (.Ok ()) := by
  intro run
  have count:=JGx_EntryReads.count JHb_World.e2
  have magic:=JHf_MagicFixed.real (JHf_ReconstructionConfiguration.seed c) err
  exact JHf_MasterFieldRefutation.source c err slot field
    (JHf_Stage2Inversion.source _ _ _ _ _ count magic run)
#print axioms source
end AspisR1.JHf_NativeMasterFieldRefutation
end
