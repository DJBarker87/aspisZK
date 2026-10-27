import LPa_Check
import LPa_Echeck
import LPa_StageLaws
set_option autoImplicit false
namespace LPa

theorem check_stage_congruence (a b : List Aeneas.Std.U8)
    (count : a.length/16 = b.length/16)
    (same : ∀ i, i < a.length/16 → Check.predicate a i = Check.predicate b i) :
    Check.loop a = Check.loop b := by
  unfold Check.loop
  rw [← count]
  apply stages_congr
  intro state i bound
  rw [same i bound]

theorem echeck_stage_congruence (a b : List Aeneas.Std.U8) (k : Bool)
    (count : a.length/32 = b.length/32)
    (same : ∀ i, i < a.length/32 → Echeck.predicate a k i = Echeck.predicate b k i) :
    Echeck.loop a k = Echeck.loop b k := by
  unfold Echeck.loop
  rw [← count]
  apply stages_congr
  intro state i bound
  rw [same i bound]
#print axioms check_stage_congruence
#print axioms echeck_stage_congruence
end LPa
