import NDO_JGg_QueryStep
import NDO_JGg_QueryArrays
set_option autoImplicit false
namespace AspisR1.JGg_QueryStep1
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
open JGg_QuerySplit

theorem source {Hash A : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (k : Blocks → Blocks → Bytes32 → Result A) :
    step (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D))
      hash 1#usize (encodeState JGg_Opening31.next0) JGg_QueryArrays.b1 JGg_QueryArrays.a1 k=
      k JGg_QueryArrays.b2 JGg_QueryArrays.a2 (encodeState JGg_Opening31.next1) := by
  apply JGg_QueryStep.source _ _ _ _ (encodeState JGg_Opening31.block1) _ _ _ _ _
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash1]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash1]
  · exact JGg_QueryArrays.b_update1
  · exact JGg_QueryArrays.a_update1
  · exact JGg_QueryArrays.state1
#print axioms source
end AspisR1.JGg_QueryStep1
