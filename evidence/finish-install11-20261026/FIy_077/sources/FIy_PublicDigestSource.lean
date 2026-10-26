import FIy_PublicDigestSuffix
set_option autoImplicit false
namespace AspisR1.FIy_PublicDigestSource
open Aeneas Aeneas.Std Result FIq_Native
open FIy_PublicDigestPrefix (Public Openings)
open FIy_FrontierStep (Selectors)

theorem factor (p : Public) (o : Openings) (s : Selectors) :
    pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=(do
      let initial ← FIy_PublicDigestPrefix.run p o s
      let (middle,src) ← pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop
        ⟨0#usize,20#usize⟩ o.z s initial p.transition.live_snapshot
      FIy_PublicDigestSuffix.run p o s middle src) := by
  unfold pool_v1.pair_forest_semantic_terminal.public_digest_lanes
    FIy_PublicDigestPrefix.run FIy_PublicDigestSuffix.run
  simp only [bind_assoc_eq,bind_tc_ok]
  rfl
#print axioms factor
end AspisR1.FIy_PublicDigestSource
