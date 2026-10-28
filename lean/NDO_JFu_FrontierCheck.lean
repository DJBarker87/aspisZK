import NDO_JFu_DigestCheck
set_option autoImplicit false
namespace AspisR1.JFu_FrontierCheck
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

@[local step] theorem digest (q : Array U32 8#usize) (canon : JFu_DigestCanonical.Canonical q) :
    pool_v1.pair_tree_profile.digest_is_canonical q ⦃ b => b=true ⦄ := by
  rw [JFu_DigestCheck.source q canon,WP.spec_ok]

theorem source (a : Array (Array U32 8#usize) 20#usize)
    (canon : ∀ i : Fin 20,JFu_DigestCanonical.Canonical
      (a.val[i.val]'(by simpa only [a.property,show (20#usize).val=20 from rfl] using i.isLt))) :
    pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize=ok (.Ok ()) := by
  have spec : pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize
      ⦃ out => out=.Ok () ⦄ := by
    unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop
    refine loop.spec_decr_nat
      (fun i : Usize => 20-i.val) (fun i : Usize => i.val≤20)
      (fun out => out=.Ok ())
      (fun i => pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i)
      0#usize ?_ ?_
    · intro i hi
      unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body
      step*
      all_goals first
        | scalar_tac
        | (simp_all;exact canon ⟨i.val,by scalar_tac⟩)
    · scalar_tac
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms digest
#print axioms source
end AspisR1.JFu_FrontierCheck
