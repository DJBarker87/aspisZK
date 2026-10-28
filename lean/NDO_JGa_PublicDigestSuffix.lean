import NDO_JGa_DigestLoop
import RPv_JGa_ArrayProperty
import RPv_FIy_PublicDigestSuffix
import NDO_JFy_FrontierCanonical
import NDO_JFu_TransitionArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_PublicDigestSuffix
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open JFy_PublicCanonical (p)

@[step] theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (d : Array field.QM31 8#usize)
    (hz : canonical o.z) (hd : canonical d) (hh : canonical s.high) (hl : canonical s.low) :
    FIy_PublicDigestSuffix.run p o s d p.transition.live_snapshot ⦃ out => canonical out ⦄ := by
  have hn := JFy_FrontierCanonical.root
  have hf := JFy_FrontierCanonical.after
  unfold FIy_PublicDigestSuffix.run
  have carry : pool_v1.pair_forest_semantic_terminal.bounded_append_carry p.transition.live_snapshot.next_pair_index=ok 1#usize := JFu_TransitionArithmetic.carry
  rw [carry]
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JGa_PublicDigestSuffix
end
