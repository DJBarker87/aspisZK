import RPt_JFo_Prepared
import Tx2N_Powers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_GammaCanonical
open Aeneas Aeneas.Std Result

theorem source : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers JFo_Prepared.value.gamma) := by
  change ((855639275 < 2147483647 ∧ 1483149559 < 2147483647) ∧
    (1898717401 < 2147483647 ∧ 1849775942 < 2147483647)) ∧
    ((1112406525 < 2147483647 ∧ 1796814865 < 2147483647) ∧
    (1838939499 < 2147483647 ∧ 418714188 < 2147483647))
  omega

#print axioms source
end AspisR1.JFo_GammaCanonical
end
