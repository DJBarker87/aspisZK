import DrvC_Program
import AuS1_Install
import GExp_FirstPair
import GExp_SecondPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Installation
open Aeneas Aeneas.Std Result

/-- The data left abstract by the adopted installed SDK, with no compatibility
or acceptance fields. This is not a replacement refinement assumption. -/
structure Configuration (F CoreError : Type) where
  adapter : AdapterRw.Ops
  currentBase : AspisR1CurrentCaller.Ops
  stageBase : VTop_Stages.Ops
  finish : AspisR1Stage2.Stage2Finish.FinishOps F
  reserved : Bool
  query : Port3_NativeQueryBody.Ops
  geometry : Port3_NativeGeometryBody.Ops CoreError
  boundaries : AspisR1PublicPreparation.FinishModel.Boundaries
  std : ClaimsUnrolledFinish.StdCalls

variable {F C : Type}

def stage (c : Configuration F C) :=
  DrvI_Installation.stage c.reserved c.query c.geometry (AuS1_Install.base c.stageBase) c.finish

def current (c : Configuration F C) := Uni_Install.current c.currentBase c.reserved c.query c.geometry

def currentInstalled (c : Configuration F C) :=
  RowShape_InstalledSlots.verifierOps (current c) c.boundaries c.std

def sdk (c : Configuration F C) :=
  DrvI_Installation.sdk c.adapter c.currentBase c.reserved c.query c.geometry
    (AuS1_Install.base c.stageBase) c.finish c.boundaries c.std

def digest (c : Configuration F C) := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdk c)
def currentDigest (c : Configuration F C) := AspisS6CurrentFirstInstallation.toDigest (digest c)

theorem cphy_dictionary (c : Configuration F C) : sdk c =
    ClaimsUnrolledSdk.sdkOps
      (Tx2I_Install.install c.adapter
        (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
          c.reserved c.query c.geometry)) c.finish)
      (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std := rfl

theorem aus1_dictionary (c : Configuration F C) : sdk c =
    SdkD_PairBatches.dictionary c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std :=
  (AuS1_Install.dictionary c.adapter c.currentBase c.stageBase c.finish c.reserved
    c.query c.geometry c.boundaries c.std).symm

theorem gexp_dictionary (c : Configuration F C) : sdk c =
    GExp_SecondPair.sdk c.adapter c.currentBase (AuS1_Install.base c.stageBase) c.finish
      c.reserved c.query c.geometry c.boundaries c.std := rfl

theorem current_dictionary (c : Configuration F C) : currentInstalled c =
    GExp_FirstCode.installed
      (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std :=
  (GExp_FirstPair.installed c.currentBase c.reserved c.query c.geometry c.boundaries c.std).symm

theorem stage_dictionary (c : Configuration F C) : stage c =
    GExp_SecondPair.base (AuS1_Install.base c.stageBase) c.finish c.reserved c.query c.geometry := rfl

theorem digest_call (c : Configuration F C) (parts : Slice (Slice U8)) :
    (currentDigest c).digest () parts = (sdk c).op43 () parts := rfl

#print axioms cphy_dictionary
#print axioms aus1_dictionary
#print axioms gexp_dictionary
#print axioms current_dictionary
#print axioms stage_dictionary
#print axioms digest_call
end AspisR1.DrvC_Installation
end
