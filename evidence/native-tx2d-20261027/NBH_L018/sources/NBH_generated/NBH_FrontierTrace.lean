import NBH_NativeFrontier
import NBH_NativeLiveFrontier
set_option autoImplicit false
noncomputable section
namespace NBH_FrontierTrace
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NBH_Frontier NBD_DigestInduction
attribute [local instance] Classical.propDecidable

def word (a : Frontier) (i : Nat) : Nat :=
  if h : i<20 then if Canonical (a.val[i]'(by have := a.property; scalar_tac)) then 0 else 2147483647 else 0

theorem good (a : Frontier) (i : Nat) (hi : i<20) :
    word a i < 2147483647 ↔ Canonical (a.val[i]'(by have := a.property; scalar_tac)) := by
  simp only [word,dif_pos hi]
  split <;> simp_all

theorem result (a : Frontier) (b : Bool) (trace : NBD_DigestTrace.Trace (word a) 0 20 b) :
    (b=true ↔ CanonicalFrom a 0) := by
  have exact := NBD_DigestTrace.exact _ _ _ _ trace
  rw [exact]
  constructor
  · intro h j _
    exact (good a j.val j.isLt).mp (h j.val (by omega) j.isLt)
  · intro h j _ hj
    exact (good a j hj).mpr (h ⟨j,hj⟩ (by omega))

theorem afterstate (a : Frontier) (b : Bool) (trace : NBD_DigestTrace.Trace (word a) 0 20 b) :
    pool_v1.pair_terminal.validate_verified_afterstate_loop a 0#usize =
    ok (if b then .Ok () else .Err .NonCanonicalAfterstate) := by
  rw [NBH_Frontier.afterstate_loop]
  have same := result a b trace
  cases b <;> simp_all

theorem live (a : Frontier) (b : Bool) (trace : NBD_DigestTrace.Trace (word a) 0 20 b) :
    pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize =
    ok (if b then .Ok () else .Err .NonCanonicalDigest) := by
  rw [NBH_LiveFrontier.live_loop]
  have same := result a b trace
  cases b <;> simp_all

theorem total (a : Frontier) : ∃ b, NBD_DigestTrace.Trace (word a) 0 20 b :=
  NBD_DigestTrace.total _ _ _

#print axioms good
#print axioms result
#print axioms afterstate
#print axioms live
#print axioms total
end NBH_FrontierTrace
