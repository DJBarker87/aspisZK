import F3U_Rehash
import S1SemanticCurrentCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_OracleDictionary
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

def current {Hash : Type} (H : Bytes → State) (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) :
    AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash :=
  {D with digest := fun _ parts => F3U_Oracle.hashv H parts}

theorem retained {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) :
    AspisR1CurrentCaller.InstalledPreparation.retainedDigest (current H D)=
      F3U_Rehash.dictionary H (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D) := rfl

#print axioms retained
end AspisR1.F3V_OracleDictionary
end
