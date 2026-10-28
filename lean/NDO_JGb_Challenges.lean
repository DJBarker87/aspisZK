import NDO_JGa_ChallengeCanonical
import NDO_JFm_Result
set_option autoImplicit false
namespace AspisR1.JGb_Challenges
open FIq_Native
open FIv_NativeValue (Canon)
theorem theta : Canon JFu_TerminalPrefix.challenges.theta := by
  change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647)
  decide
#print axioms theta
theorem mu : Canon JFu_TerminalPrefix.challenges.mu := by
  change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647)
  decide
#print axioms mu
end AspisR1.JGb_Challenges
