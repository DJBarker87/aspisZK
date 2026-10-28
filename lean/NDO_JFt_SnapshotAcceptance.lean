import NDO_JFu_PublicBindings
import NDO_JFu_PublicIndices
import NDO_JFu_SnapshotValidator
import NDO_JFu_DigestSliceCanonical
set_option autoImplicit false
namespace AspisR1.JFt_SnapshotAcceptance
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem source (s : PoolV1PairLiveSnapshotV1)
    (pool : s.pool=JFu_PublicBindings.pool) (domain : s.deployment_domain=JFu_PublicBindings.domain)
    (sequence : s.sequence=13#u64) (index : s.next_pair_index=13#u64)
    (root : AspisS6NativeSnapshotReadDigest.read_digest (JFu_PublicRange.segment 304 32 (by decide))=
      ok (.Ok s.current_root))
    (frontier : ∀ i : Fin 20,AspisS6NativeSnapshotReadDigest.read_digest
      (JFu_PublicRange.segment (336+32*i.val) 32 (by have h:=i.isLt;omega))=
      ok (.Ok (s.frontier.val[i.val]'(by simpa only [s.frontier.property,show (20#usize).val=20 from rfl] using i.isLt)))) :
    validate_pool_v1_pair_live_snapshot_v1 s=ok (.Ok ()) := by
  apply JFu_SnapshotValidator.source s
  · rw [pool];exact JFu_PublicBindings.pool_nonzero
  · rw [domain];exact JFu_PublicBindings.domain_nonzero
  · rw [sequence,index]
  · rw [index];decide
  · exact JFu_DigestSliceCanonical.source _ _ root
  · intro i
    exact JFu_DigestSliceCanonical.source _ _ (frontier i)

#print axioms source
end AspisR1.JFt_SnapshotAcceptance
