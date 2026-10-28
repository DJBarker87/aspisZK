import PV_B3P_HelperEffects224
namespace PV_B3P_HelperOrder224
open Aeneas Aeneas.Std PV_B3P_RustResult PV_B3P_HelperEffects224
set_option autoImplicit false

theorem four_endpoints {F W E : Type} (ops : Operations F W E) (chi : F)
    (p0 p1 c0 c1 : F × W) :
    row ops chi p0 p1 c0 c1 =
      bindR (endpoint ops false chi ops.zero p0.1 p0.2) (fun v0 =>
      bindR (endpoint ops false chi v0 p1.1 p1.2) (fun v1 =>
      bindR (endpoint ops true chi v1 c0.1 c0.2) (fun v2 =>
        endpoint ops true chi v2 c1.1 c1.2))) := by
  rw [row,two_slots,bindR_assoc]
  congr 1
  funext v
  congr 1
  funext v1
  exact two_slots ops true chi v1 c0 c1

-- These laws cover all Result channels without assuming arithmetic totality.
theorem denominator_failure {F W E : Type} (ops : Operations F W E) (consumer : Bool)
    (chi value operand : F) (weight : W) (e : Aeneas.Std.Error)
    (ha : ops.active weight = true) (hd : ops.sub chi operand = .fail e) :
    endpoint ops consumer chi value operand weight = .fail e := by
  simp only [endpoint,ha,↓reduceIte,hd,bind_tc_fail]

theorem denominator_divergence {F W E : Type} (ops : Operations F W E) (consumer : Bool)
    (chi value operand : F) (weight : W)
    (ha : ops.active weight = true) (hd : ops.sub chi operand = .div) :
    endpoint ops consumer chi value operand weight = .div := by
  simp only [endpoint,ha,↓reduceIte,hd,bind_tc_div]

theorem producer_rejection {F W E : Type} (ops : Operations F W E) (chi : F)
    (p0 p1 c0 c1 : F × W)
    (h : endpoint ops false chi ops.zero p0.1 p0.2 = .ok (.Err ops.imbalance)) :
    row ops chi p0 p1 c0 c1 = .ok (.Err ops.imbalance) := by
  rw [four_endpoints,h]
  rfl

theorem consumer_rejection {F W E : Type} (ops : Operations F W E) (chi v : F)
    (p0 p1 c0 c1 : F × W)
    (hprod : slots ops false chi ops.zero [p0,p1] = .ok (.Ok v))
    (hcons : endpoint ops true chi v c0.1 c0.2 = .ok (.Err ops.imbalance)) :
    row ops chi p0 p1 c0 c1 = .ok (.Err ops.imbalance) := by
  rw [row,hprod]
  simp only [bindR,two_slots,hcons]

#print axioms four_endpoints
#print axioms denominator_failure
#print axioms denominator_divergence
#print axioms producer_rejection
#print axioms consumer_rejection
end PV_B3P_HelperOrder224
