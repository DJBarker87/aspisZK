import NBH_LiveFrontier
set_option autoImplicit false
noncomputable section
namespace NBH_NativeLiveFrontier
open Aeneas Aeneas.Std Result ControlFlow WP AspisR1TerminalDecoder
open NBH_Frontier NBD_DigestInduction
attribute [local instance] Classical.propDecidable
abbrev Error := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1

def step (a : Frontier) (i : Nat) : Nat × Option Error :=
  if h : i < 20 then
    if Canonical (a.val[i]'(by have := a.property; scalar_tac)) then (i+1,none)
    else (i,some .NonCanonicalDigest)
  else (i,none)

def observe (i : Usize) : ControlFlow Usize (core.result.Result Unit Error) → Nat × Option Error
  | .cont n => (n.val,none)
  | .done (.Ok _) => (i.val,none)
  | .done (.Err e) => (i.val,some e)

theorem source (a : Frontier) (i : Usize) (hi : i.val ≤ 20) :
    (do let out ← pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i
        ok (observe i out)) = ok (step a i.val) := by
  have spec : pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i
      ⦃ out => observe i out = step a i.val ⦄ := by
    unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body
    simp only [NBD_DigestInduction.source]
    step*
    all_goals simp_all [observe,step]
    all_goals scalar_tac
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists spec
  simp only [call,bind_tc_ok,same]

#print axioms source
end NBH_NativeLiveFrontier
