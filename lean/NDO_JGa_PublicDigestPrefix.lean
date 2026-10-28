import NDO_JGa_DigestLoop
import RPv_FIy_PublicDigestPrefix
import NDO_JFy_PublicCanonical
import RPv_JFy_ZeroArrays
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
  have recipient : p.recipient=some JFt_Digest45.value := rfl
  have hr := JFy_PublicCanonical.recipient _ recipient
  have hc := JFy_PublicCanonical.change
  have zero := JFy_ZeroArrays.source 8#usize
  unfold FIy_PublicDigestPrefix.run
  rw [recipient]
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JGa_PublicDigestPrefix
end
