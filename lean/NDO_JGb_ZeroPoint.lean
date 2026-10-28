import NDO_JGb_Challenges
import NDO_JFy_PointCanonical
set_option autoImplicit false
namespace AspisR1.JGb_ZeroPoint
open Aeneas Aeneas.Std FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
theorem source : canonical JFu_TerminalPrefix.challenges.zc := by
  intro x hx
  simp only [JFu_TerminalPrefix.challenges,FIq_Carriers.toChallenges,FIq_Carriers.mapArray,
    JFm_Begin.challenges,JFm_Begin.z10,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647)
  all_goals decide
#print axioms source
end AspisR1.JGb_ZeroPoint
