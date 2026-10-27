import JGa_DigestLoop
import FIy_PublicDigestPrefix
import JFy_PublicCanonical
import JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_PublicDigestPrefix
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open JFy_PublicCanonical (p)

@[step] theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (hz : canonical o.z)
    (hh : canonical s.high) (hl : canonical s.low) :
    FIy_PublicDigestPrefix.run p o s ⦃ out => canonical out ⦄ := by
  have ha := JFy_PublicCanonical.anchor
  have hn := JFy_PublicCanonical.nullifier
  have hr := JFy_PublicCanonical.recipient
  have hc := JFy_PublicCanonical.change
  have zero := JFy_ZeroArrays.source 8#usize
  unfold FIy_PublicDigestPrefix.run
  step* <;> first | assumption | scalar_tac | exact hr _ (by assumption)
#print axioms source
end AspisR1.JGa_PublicDigestPrefix
end
