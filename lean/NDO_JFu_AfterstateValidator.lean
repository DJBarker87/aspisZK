import NDO_JFu_AfterstateFrontier
import NDO_JFu_SnapshotValidator
set_option autoImplicit false
namespace AspisR1.JFu_AfterstateValidator
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_terminal

theorem source (s : PoolV1PairVerifiedAfterstateV1)
    (positive : s.next_pair_index.val>0) (small : s.next_pair_index.val≤1048576)
    (root : JFu_DigestCanonical.Canonical s.next_root)
    (frontier : ∀ i : Fin 20,JFu_DigestCanonical.Canonical
      (s.next_frontier.val[i.val]'(by simpa only [s.next_frontier.property,show (20#usize).val=20 from rfl] using i.isLt))) :
    validate_verified_afterstate s=ok (.Ok ()) := by
  unfold validate_verified_afterstate
  have nonzero : s.next_pair_index≠0#u64 := by scalar_tac
  have bounded : ¬s.next_pair_index>1048576#u64 := by scalar_tac
  simp only [if_neg nonzero,JFu_SnapshotValidator.capacity,bind_tc_ok,if_neg bounded]
  rw [JFu_DigestCheck.source s.next_root root,bind_tc_ok]
  simp only [↓reduceIte]
  exact JFu_AfterstateFrontier.source s.next_frontier frontier

#print axioms source
end AspisR1.JFu_AfterstateValidator
