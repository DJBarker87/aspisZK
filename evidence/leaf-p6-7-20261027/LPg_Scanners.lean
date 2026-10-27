import LPg_Geometry
import LPc_CallerBounds
set_option autoImplicit false
namespace LPg
/-- The local step association remains explicit; no native whole-loop result is assumed. -/
theorem echeck_stages (bs : List Aeneas.Std.U8) (k : Bool) (size : bs.length = 928)
    (native : Bool → Nat → Bool)
    (step : ∀ good i, i < 29 → native good i = (good && LPa.Echeck.predicate bs k i)) :
    LPa.stages native true 29 = LPa.Echeck.loop bs k := by
  unfold LPa.Echeck.loop
  rw [size]
  exact LPa.stages_congr _ _ _ _ step
/-- Same induction for compact's 29 low-half checks. -/
theorem check_stages (bs : List Aeneas.Std.U8) (size : bs.length = 464)
    (native : Bool → Nat → Bool)
    (step : ∀ good i, i < 29 → native good i = (good && LPa.Check.predicate bs i)) :
    LPa.stages native true 29 = LPa.Check.loop bs := by
  unfold LPa.Check.loop
  rw [size]
  exact LPa.stages_congr _ _ _ _ step
#print axioms echeck_stages
#print axioms check_stages
end LPg
