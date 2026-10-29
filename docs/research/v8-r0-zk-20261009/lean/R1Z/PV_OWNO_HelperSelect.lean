import R1Z.PV_OWNO_HelperPush
set_option autoImplicit false
namespace R1Z.PV_OWNO_HelperSelect
open PV_OWNK_TowerCanon PV_OWNO_HelperArrays

/-- Upstream registry errors propagate unchanged. ActivePole is mapped to
CopyImbalance only by the selected outer helper, after its ordered traversal. -/
def selected {E : Type} (imbalance : E) (inverse : Q → Option Q) (chi : Q)
 (rows : Except E (List CopyRow)) : Except E (List Q) :=
 match rows with
 | .error e => .error e
 | .ok rs => match PV_OWNO_HelperPush.run inverse chi 0 rs [] with
   | .error _ => .error imbalance
   | .ok out => .ok out

theorem successful_canonical {E : Type} (imbalance : E)
 (inverse : Q → Option Q) (chi : Q) (rows : Except E (List CopyRow)) (out : List Q)
 (h : selected imbalance inverse chi rows = .ok out) : ∀ q ∈ out, Canon q := by
 cases rows with
 | error e => cases h
 | ok rs =>
  cases hr : PV_OWNO_HelperPush.run inverse chi 0 rs [] with
  | error e => simp only [selected,hr] at h; cases h
  | ok values =>
   simp only [selected,hr] at h
   have he : values = out := Except.ok.inj h
   exact he ▸ PV_OWNO_HelperPush.successful_canonical inverse chi 0 rs [] values
    (by intro q hq; cases hq) hr

#print axioms successful_canonical
end R1Z.PV_OWNO_HelperSelect
