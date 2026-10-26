import F3U_Oracle
import GExp_SecondSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_StageDictionary
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def ideal {Hash : Type} (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) :
    VTop_Stages.aspis_core.digest.Digest32 Hash :=
  {D with digest := fun _ parts => F3U_Oracle.hashv H parts}

theorem digest {Hash : Type} (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (parts : SdkC_Source.Parts) :
    (ideal H D).digest hash parts=F3U_Oracle.hashv H parts := rfl

#print axioms digest
end AspisR1.F3V_StageDictionary
end
