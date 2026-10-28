import NDO_JGg_QueryStep1
import NDO_JGg_QueryStep2
import NDO_JGg_QueryStep3
import NDO_JGg_QueryStep4
import NDO_JGg_QueryStep5
import NDO_JGg_QueryStep6
import NDO_JGg_QueryStep7
import NDO_JGg_QueryInitial
set_option autoImplicit false
namespace AspisR1.JGg_QueryLater
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge JGg_QuerySplit

theorem source {Hash A : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (k : Blocks → Blocks → Result A) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    later D0 hash JGg_QueryArrays.b1 JGg_QueryArrays.a1 (encodeState JGg_Opening31.next0) k=
      k JGg_QueryArrays.b8 JGg_QueryArrays.a8 := by
  dsimp only
  unfold later
  rw [JGg_QueryStep1.source]
  rw [JGg_QueryStep2.source]
  rw [JGg_QueryStep3.source]
  rw [JGg_QueryStep4.source]
  rw [JGg_QueryStep5.source]
  rw [JGg_QueryStep6.source]
  rw [JGg_QueryStep7.source]
#print axioms source
end AspisR1.JGg_QueryLater
