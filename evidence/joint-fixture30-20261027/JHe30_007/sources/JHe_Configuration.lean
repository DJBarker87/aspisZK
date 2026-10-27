import JGx_Configuration
import JGr_Geometry
import IDa_Deployed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_Configuration
open Aeneas Aeneas.Std Result DrvC_Installation

def missing (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) : IDa_Deployed.Uninstalled Unit where
  adapter := {adapter with op43:=S2W_DigestExtraction.digest (F3U_Oracle.hashv JFp_SHADigest.digest)}
  currentBase := JGp_Allocation.base JGp_Seeds.base
  stageBase := stage
  reserved := true
  query := JGp_Seeds.query
  geometry := JGp_Seeds.geometry

def value (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  IDa_Deployed.deployedConfiguration (missing adapter stage) () (.Ok ())

theorem current (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    DrvC_Installation.currentInstalled (value adapter stage)=JGr_Geometry.installed := by
  rfl
#print axioms current

theorem digest (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    DrvC_Installation.currentDigest (value adapter stage)=JGr_Geometry.digest := by
  rfl
#print axioms digest
end AspisR1.JHe_Configuration
end
