import NDO_JFy_PointCanonical
import RPv_JFy_Specs
set_option autoImplicit false
namespace AspisR1.JGa_ChallengeCanonical
open Aeneas Aeneas.Std FIq_Native
open FIv_NativeValue (Canon)

theorem lambda : Canon JFu_TerminalPrefix.challenges.lambda := by
  change (399501241<2147483647 ∧ 284689285<2147483647) ∧ (1852519329<2147483647 ∧ 449773828<2147483647)
  omega
#print axioms lambda

theorem chi : Canon JFu_TerminalPrefix.challenges.chi := by
  change (941725965<2147483647 ∧ 710616451<2147483647) ∧ (1814298802<2147483647 ∧ 371706036<2147483647)
  omega
#print axioms chi
end AspisR1.JGa_ChallengeCanonical
