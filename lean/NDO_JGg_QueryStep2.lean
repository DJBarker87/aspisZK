import NDO_JGg_QueryStep
import NDO_JGg_QueryArrays
set_option autoImplicit false
namespace AspisR1.JGg_QueryStep2
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
open JGg_QuerySplit

theorem source {Hash A : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (k : Blocks → Blocks → Bytes32 → Result A) :
    step (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D))
      hash 2#usize (encodeState JGg_Opening31.next1) JGg_QueryArrays.b2 JGg_QueryArrays.a2 k=
      k JGg_QueryArrays.b3 JGg_QueryArrays.a3 (encodeState JGg_Opening31.next2) := by
  apply JGg_QueryStep.source _ _ _ _ (encodeState JGg_Opening31.block2) _ _ _ _ _
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash2]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash2]
  · exact JGg_QueryArrays.b_update2
  · exact JGg_QueryArrays.a_update2
  · exact JGg_QueryArrays.state2
#print axioms source
end AspisR1.JGg_QueryStep2
