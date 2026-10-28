import R1Z.PV_RunJoin_OwnedCarry31
import R1Z.PV_RunJoin_UniversalTreeFrame22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicCarry31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
variable {K : Type} [Field K] [CharP K 2147483647]

theorem carry (pub : R0P.Public K) (leafMeaning : R0P.Digest K)
    (tree next : incremental_merkle.IncrementalMerkleTreeV1)
    (leaf : Digest) (roots : Roots) (receipt : incremental_merkle.AppendOneV1)
    (hi : tree.next_leaf_index.val = pub.nextPairIndex)
    (hc : Canon8 leaf) (hm : digK leaf = leafMeaning)
    (hf : ∀ j : Fin 20, digK tree.frontier.val[j.val]! = pub.snapshotFrontier j)
    (h : incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots tree leaf roots = ok (.Ok (next,receipt)))
    (small : R0P.digestCarry pub.nextPairIndex < 20) :
    digK next.frontier.val[R0P.digestCarry pub.nextPairIndex]! =
      AspisR1.AppendPath.pathPrefix pub leafMeaning (R0P.digestCarry pub.nextPairIndex) := by
  unfold incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots at h
  pv_peel h with constructed hctor
  cases constructed with
  | Err error =>
    change (ok (.Err error) : Result (core.result.Result _ _)) = ok (.Ok (next,receipt)) at h
    cases h
  | Ok owned =>
    have frame := construct tree.next_leaf_index tree.root tree.frontier roots owned hctor
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    pv_peel h with appended ha
    cases appended with
    | Err error =>
      change (ok (.Err error) : Result (core.result.Result _ _)) = ok (.Ok (next,receipt)) at h
      cases h
    | Ok pair =>
      rcases pair with ⟨ownedNext,rec⟩
      have fields := PV_RunJoin_OwnedCarry31.carry pub leafMeaning owned ownedNext leaf rec
        (by simpa only [frame.1] using hi) hc hm (by simpa only [frame.1] using hf) ha small
      change (ok (.Ok (ownedNext.inner,rec)) : Result (core.result.Result
        (incremental_merkle.IncrementalMerkleTreeV1 × incremental_merkle.AppendOneV1)
        incremental_merkle.PoolV1TreeError)) = ok (.Ok (next,receipt)) at h
      have same := core.result.Result.Ok.inj (Result.ok.inj h)
      cases same
      exact fields
#print axioms carry
end R1Z.PV_RunJoin_PublicCarry31
