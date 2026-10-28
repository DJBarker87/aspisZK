import NDO_JGp_QueryNumeric
import NDO_JGg_QueryCalls
set_option autoImplicit false
namespace AspisR1.JGp_QueryCalls
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
open AspisR1CurrentCaller.BorrowedClaimPrepared

theorem source {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    QueriesModel.queries closedHashQueries D0
      (⟨encodeState JGg_Opening31.before,hash⟩ : transcript.Transcript H) 31#u8 JGg_Opening31.payload=
      ok (.Ok JFq_Queries.value,(⟨encodeState JGg_Opening31.next2,hash⟩ : transcript.Transcript H)) := by
  dsimp only
  rw [JGg_QueryFactor.source_eq,JGg_QueryInitial.source D hash,JGg_QueryLater.source D hash]
  apply JGg_QueryFinish.source
  rw [JGg_QueryArrays.blocks,JGg_QueryArrays.advances]
  exact JGp_QueryNumeric.source
#print axioms source
end AspisR1.JGp_QueryCalls
