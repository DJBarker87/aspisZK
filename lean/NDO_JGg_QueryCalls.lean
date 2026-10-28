import NDO_JGg_QueryFactor
import NDO_JGg_QueryLater
import NDO_JGg_QueryFinish
set_option autoImplicit false
namespace AspisR1.JGg_QueryCalls
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
open AspisR1CurrentCaller.BorrowedClaimPrepared

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q,QueriesModel.queries closedHashQueries D0
      (⟨encodeState JGg_Opening31.before,hash⟩ : transcript.Transcript Hash) 31#u8 JGg_Opening31.payload=
      ok (.Ok q,(⟨encodeState JGg_Opening31.next2,hash⟩ : transcript.Transcript Hash)) := by
  dsimp only
  obtain ⟨q,decode⟩ := JGg_QueryDecode.source
  refine ⟨q,?_⟩
  rw [JGg_QueryFactor.source_eq,JGg_QueryInitial.source D hash,JGg_QueryLater.source D hash]
  apply JGg_QueryFinish.source
  rw [JGg_QueryArrays.blocks,JGg_QueryArrays.advances]
  exact decode
#print axioms source
end AspisR1.JGg_QueryCalls
