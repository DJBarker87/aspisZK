import NDO_JGx_Configuration
import NDO_JGr_Geometry
import NDO_JHe_InstalledData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_Configuration
open Aeneas Aeneas.Std Result DrvC_Installation

def missing (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) : JHe_InstalledData.Uninstalled Unit where
  adapter := {adapter with op42:=fun x=>ok x,op43:=S2W_DigestExtraction.digest (F3U_Oracle.hashv JFp_SHADigest.digest)}
  currentBase := JGp_Allocation.base JGp_Seeds.base
  stageBase := stage
  reserved := true
  query := JFr_TX2_DotsBinding.ops JGp_Seeds.query
  geometry := JGp_Seeds.geometry

def value (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  JHe_InstalledData.deployedConfiguration (missing adapter stage) () (.Ok ())

/-- WAdm content interpretation is a distinct writer installation; no full
SDK/deployed equality is claimed by this data declaration. -/
def contentCurrent (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  {(DrvC_Installation.currentInstalled (value adapter stage)) with op16:=WAdm_Install.writer}
end AspisR1.JHe_Configuration
end
