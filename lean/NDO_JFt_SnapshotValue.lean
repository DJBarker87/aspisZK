import NDO_JFt_Digest01
import NDO_JFt_Digest02
import NDO_JFt_Digest03
import NDO_JFt_Digest04
import NDO_JFt_Digest05
import NDO_JFt_Digest06
import NDO_JFt_Digest07
import NDO_JFt_Digest08
import NDO_JFt_Digest09
import NDO_JFt_Digest10
import NDO_JFt_Digest11
import NDO_JFt_Digest12
import NDO_JFt_Digest13
import NDO_JFt_Digest14
import NDO_JFt_Digest15
import NDO_JFt_Digest16
import NDO_JFt_Digest17
import NDO_JFt_Digest18
import NDO_JFt_Digest19
import NDO_JFt_Digest20
import NDO_JFt_Digest21
import NDO_JFt_SnapshotAcceptance
import NDO_JFt_Metadata
set_option autoImplicit false
namespace AspisR1.JFt_SnapshotValue
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

def value : PoolV1PairLiveSnapshotV1 :=
  {pool:=JFu_PublicBindings.pool,deployment_domain:=JFu_PublicBindings.domain,
   sequence:=13#u64,next_pair_index:=13#u64,current_root:=JFt_Digest01.value,
   frontier:=Array.make 20#usize [JFt_Digest02.value,JFt_Digest03.value,JFt_Digest04.value,JFt_Digest05.value,JFt_Digest06.value,JFt_Digest07.value,JFt_Digest08.value,JFt_Digest09.value,JFt_Digest10.value,JFt_Digest11.value,JFt_Digest12.value,JFt_Digest13.value,JFt_Digest14.value,JFt_Digest15.value,JFt_Digest16.value,JFt_Digest17.value,JFt_Digest18.value,JFt_Digest19.value,JFt_Digest20.value,JFt_Digest21.value]}

theorem frontier : ∀ i : Fin 20,AspisS6NativeSnapshotReadDigest.read_digest
    (JFu_PublicRange.segment (336+32*i.val) 32 (by have h:=i.isLt;omega))=
    ok (.Ok (value.frontier.val[i.val]'(by simp only [value,Array.make];exact i.isLt))) := by
  intro i
  fin_cases i
  · exact JFt_Digest02.source
  · exact JFt_Digest03.source
  · exact JFt_Digest04.source
  · exact JFt_Digest05.source
  · exact JFt_Digest06.source
  · exact JFt_Digest07.source
  · exact JFt_Digest08.source
  · exact JFt_Digest09.source
  · exact JFt_Digest10.source
  · exact JFt_Digest11.source
  · exact JFt_Digest12.source
  · exact JFt_Digest13.source
  · exact JFt_Digest14.source
  · exact JFt_Digest15.source
  · exact JFt_Digest16.source
  · exact JFt_Digest17.source
  · exact JFt_Digest18.source
  · exact JFt_Digest19.source
  · exact JFt_Digest20.source
  · exact JFt_Digest21.source

theorem validated : validate_pool_v1_pair_live_snapshot_v1 value=ok (.Ok ()) :=
  JFt_SnapshotAcceptance.source value rfl rfl rfl rfl JFt_Digest01.source frontier

#print axioms frontier
#print axioms validated
end AspisR1.JFt_SnapshotValue
