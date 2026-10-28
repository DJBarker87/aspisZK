import R1Z.PV_RunJoin_LateAppendFrame31
import R1Z.PV_RunJoin_PublicCarry31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LateAppendCarry31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
variable {K : Type} [Field K] [CharP K 2147483647]

theorem carry (pub : R0P.Public K) (leafMeaning : R0P.Digest K)
    (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (afterstate : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (hi : snapshot.next_pair_index.val = pub.nextPairIndex)
    (hc : Canon8 leaf) (hm : digK leaf = leafMeaning)
    (hf : ∀ j : Fin 20, digK snapshot.frontier.val[j.val]! = pub.snapshotFrontier j)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok afterstate))
    (small : R0P.digestCarry pub.nextPairIndex < 20) :
    digK afterstate.next_frontier.val[R0P.digestCarry pub.nextPairIndex]! =
      AspisR1.AppendPath.pathPrefix pub leafMeaning (R0P.digestCarry pub.nextPairIndex) := by
  obtain ⟨roots,tree,next,receipt,hctor,happend,hfront⟩ := PV_RunJoin_LateAppendFrame31.returned records snapshot leaf afterstate h
  have frame := PV_RunJoin_LateAppendFrame31.construct _ _ _ _ tree hctor
  have hcarr := PV_RunJoin_PublicCarry31.carry pub leafMeaning tree next leaf roots receipt
    (by simpa only [frame] using hi) hc hm (by simpa only [frame] using hf) happend small
  rw [hfront]
  exact hcarr
#print axioms carry
end R1Z.PV_RunJoin_LateAppendCarry31
