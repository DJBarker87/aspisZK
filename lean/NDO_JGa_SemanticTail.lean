import NDO_JGa_ValueLanes
import NDO_JGa_PublicDigest
import NDO_JFy_Occupancy
import NDO_JFy_ScalarSuffix
import NDO_JFy_SemanticPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_SemanticTail
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open JFy_PublicCanonical (p)
open pool_v1.pair_forest_semantic_terminal

theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (path : Array field.QM31 24#usize)
    (hz : canonical o.z) (hb : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hh : canonical s.high) (hl : canonical s.low) (hp : canonical path) :
    ∃ out,JFy_SemanticPrefix.tail p o s path=ok out ∧ canonical out := by
  obtain ⟨v,hv,hvc⟩ := WP.spec_imp_exists (JGa_ValueLanes.source path o s hp hz hb hx hh hl)
  obtain ⟨oc,ho,hoc⟩ := WP.spec_imp_exists (JFy_Occupancy.source v o s hvc hz hh hl)
  obtain ⟨d,hd,hdc⟩ := WP.spec_imp_exists (JGa_PublicDigest.source o s hz hh hl)
  obtain ⟨p5,h5,h5c⟩ := WP.spec_imp_exists (JFy_Preweighted.source oc 84#usize d (by decide) (by decide) hoc hdc)
  obtain ⟨out,hout,houtc⟩ := JFy_ScalarSuffix.source o s p5 hz hh hl h5c
  refine ⟨out,?_,houtc⟩
  unfold JFy_SemanticPrefix.tail
  rw [hv,bind_tc_ok,ho,bind_tc_ok,hd,bind_tc_ok,h5,bind_tc_ok]
  exact hout
#print axioms source
end AspisR1.JGa_SemanticTail
end
