import NDO_JHe_Configuration
import NDO_JHe_SdkLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_Natives
open Aeneas Aeneas.Std Result DrvC_Installation

def configuration (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  JHe_Configuration.value (JHe_SdkLeaves.install base) stage

def sdk (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  DrvC_Installation.sdk (configuration base stage)

def first (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) : S2W_ExtractionBoundary.First :=
  AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk base stage)
def second (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) : S2W_ExtractionBoundary.Second :=
  AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk base stage)

def data1 : Slice U8 := ⟨[3#u8,10#u8],by scalar_tac⟩

theorem extraction (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    S2W_DigestExtraction.AeneasExtraction (sdk base stage)
      (first base stage) (second base stage) (F3U_Oracle.hashv JFp_SHADigest.digest) :=
  ⟨by intros;rfl,by intros;rfl,by intros;rfl⟩
#print axioms extraction
end AspisR1.JHe_Natives
end
