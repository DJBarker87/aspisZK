import RPt_JFo_Prepared
import SAQ_LineQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_AccumulatorCanonical
open Aeneas Aeneas.Std Result

theorem rhs : Port4C_QueryArithmetic.CanonE JFo_Prepared.accumulator.rhs := by
  change (1460949651<2147483647 ∧ 1897962060<2147483647 ∧ 2049955535<2147483647 ∧ 440526196<2147483647) ∧
    (1936630531<2147483647 ∧ 105592648<2147483647 ∧ 1567937285<2147483647 ∧ 2130692216<2147483647)
  omega

theorem power : Port3_FlushInstall.Canonical JFo_Prepared.accumulator.power := by
  change 1007926423<2147483647 ∧ 526023474<2147483647 ∧ 347718395<2147483647 ∧ 268326460<2147483647
  omega

theorem rho : Port3_FlushInstall.Canonical JFo_Prepared.value.rho := by
  change 1497225503<2147483647 ∧ 277942247<2147483647 ∧ 877802089<2147483647 ∧ 1707877402<2147483647
  omega

#print axioms rhs
#print axioms power
#print axioms rho
end AspisR1.JFn_AccumulatorCanonical
end
