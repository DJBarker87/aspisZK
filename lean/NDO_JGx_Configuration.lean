import NDO_JGx_StageDictionary
import RPz7_FIp_Install
import F3U_Oracle
import NDO_JFn_HashBoundary
import NDO_JFp_SHADigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Configuration
open Aeneas Aeneas.Std Result DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def seed {C : Type} (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  {c with reserved:=true,adapter:={c.adapter with op43:=S2W_DigestExtraction.digest (F3U_Oracle.hashv JFp_SHADigest.digest)}}

def value {C : Type} (c : Configuration FIo_Install.W C) (err : C) :=
  FIp_Install.configuration err (seed c) (.Ok ())

theorem stage {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    DrvC_Installation.stage (value c err)=JGx_StageDictionary.source c.stageBase c.finish err c.geometry c.query := by
  cases c
  rfl
#print axioms stage

theorem digest {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    DrvC_Installation.digest (value c err)=
      JFn_HashBoundary.dictionary JFp_SHADigest.digest (DrvC_Installation.digest (value c err)) := by
  rfl
#print axioms digest
end AspisR1.JGx_Configuration
end
