import NDO_JGa_PublicDigestPrefix
import NDO_JGa_PublicDigestSuffix
import NDO_JGa_FrontierLoop
import RPv_FIy_PublicDigestSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_PublicDigest
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open JFy_PublicCanonical (p)

@[step] theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (hz : canonical o.z)
    (hh : canonical s.high) (hl : canonical s.low) :
    pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s ⦃ out => canonical out ⦄ := by
  obtain ⟨d,hd,hdc⟩ := WP.spec_imp_exists (JGa_PublicDigestPrefix.source o s hz hh hl)
  obtain ⟨middle,hm,hmc⟩ := JGa_FrontierLoop.source 20 ⟨0#usize,20#usize⟩ o.z s d p.transition.live_snapshot rfl rfl hz hdc hh hl JFy_FrontierCanonical.before
  unfold FIy_FrontierLoopStep.loop at hm
  obtain ⟨out,ho,hoc⟩ := WP.spec_imp_exists (JGa_PublicDigestSuffix.source o s middle hz hmc hh hl)
  have call : pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok out := by
    rw [FIy_PublicDigestSource.factor,hd,bind_tc_ok,hm,bind_tc_ok]
    exact ho
  rw [call]
  exact hoc
#print axioms source
end AspisR1.JGa_PublicDigest
end
