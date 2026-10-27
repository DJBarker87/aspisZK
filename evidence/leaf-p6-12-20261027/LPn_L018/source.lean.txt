import LPl_G_Geometry
import LPl_C_CallerBounds
set_option autoImplicit false
namespace LPl_G
/-- The local step association remains explicit; no native whole-loop result is assumed. -/
theorem echeck_stages (bs : List Aeneas.Std.U8) (k : Bool) (size : bs.length = 928)
    (native : Bool → Nat → Bool)
    (step : ∀ good i, i < 29 → native good i = (good && LPl_A.Echeck.predicate bs k i)) :
    LPl_A.stages native true 29 = LPl_A.Echeck.loop bs k := by
  unfold LPl_A.Echeck.loop
  rw [size]
  exact LPl_A.stages_congr _ _ _ _ step
/-- Same induction for compact's 29 low-half checks. -/
theorem check_stages (bs : List Aeneas.Std.U8) (size : bs.length = 464)
    (native : Bool → Nat → Bool)
    (step : ∀ good i, i < 29 → native good i = (good && LPl_A.Check.predicate bs i)) :
    LPl_A.stages native true 29 = LPl_A.Check.loop bs := by
  unfold LPl_A.Check.loop
  rw [size]
  exact LPl_A.stages_congr _ _ _ _ step
#print axioms echeck_stages
#print axioms check_stages
end LPl_G
