import RPt_JFo_Prepared
import Tx2N_Powers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_GammaCanonical
open Aeneas Aeneas.Std Result

theorem source : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers JFo_Prepared.value.gamma) := by
  change ((855536485 < 2147483647 ∧ 461474173 < 2147483647) ∧
    (798342634 < 2147483647 ∧ 1775607996 < 2147483647)) ∧
    ((2127456138 < 2147483647 ∧ 1342862068 < 2147483647) ∧
    (1305843559 < 2147483647 ∧ 1845381817 < 2147483647))
  omega

#print axioms source
end AspisR1.JFo_GammaCanonical
end
