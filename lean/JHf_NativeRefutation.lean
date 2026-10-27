import JHf_Stage2Inversion
import JHf_MagicFixed
import JHf_ValidationRefutation
import JGx_EntryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_NativeRefutation
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

def native {C : Type} (c : Configuration FIo_Install.W C) (err : C) : S2W_ExtractionBoundary.Second :=
  AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk (JHf_ReconstructionConfiguration.value c err))

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (slot : S2W_ExtractionBoundary.Slot)
    (faithful : JHf_ValidationRefutation.Faithful (sdk (JHf_ReconstructionConfiguration.value c err))
      CPH_Program.verifier (JHb_World.e2.second secondSizes)) :
    native c err CPH_Program.verifier (JHb_World.e2.second secondSizes) JHb_DataRequest.value slot≠ok (.Ok ()) := by
  intro run
  have count:=JGx_EntryReads.count JHb_World.e2
  have magic:=JHf_MagicFixed.real (JHf_ReconstructionConfiguration.seed c) err
  exact JHf_ValidationRefutation.source c err slot faithful
    (JHf_Stage2Inversion.source _ _ _ _ _ count magic run)
#print axioms source
end AspisR1.JHf_NativeRefutation
end
