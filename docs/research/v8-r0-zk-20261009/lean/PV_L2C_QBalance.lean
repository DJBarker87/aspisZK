import PV_L2C_NativeQ
import PV_L2C_NativeBalance
set_option autoImplicit false
namespace PV_L2C_QBalance
open PV_L2C_NativeQ

def foldQ : List Q → Q → Q
 | [], s => s
 | x::xs,s => foldQ xs (addQ s x)

def rebalanceQ (before after : List Q) : List Q :=
  before ++ subQ zero (foldQ (before++after) zero) :: after

theorem fold_component (xs : List Q) (s : Q) (i : Fin 4) :
    foldQ xs s i=PV_L2C_NativeFold.fold (xs.map (fun q => q i)) (s i) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (addQ s x)
#print axioms fold_component

theorem rebalance_component (before after : List Q) (i : Fin 4) :
    (rebalanceQ before after).map (fun q => q i)=
      PV_L2C_NativeBalance.rebalance (before.map (fun q => q i))
        (after.map (fun q => q i)) := by
  simp only [rebalanceQ,List.map_append,List.map_cons,subQ,zero,fold_component,
    PV_L2C_NativeBalance.rebalance]
#print axioms rebalance_component

theorem rebalance_audit (before after : List Q)
    (hb : ∀ q ∈ before, Canonical q) (ha : ∀ q ∈ after, Canonical q) :
    foldQ (rebalanceQ before after) zero=zero := by
  funext i
  rw [fold_component,rebalance_component]
  apply PV_L2C_NativeBalance.audit_zero
  · intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hb q hq i
  · intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact ha q hq i
#print axioms rebalance_audit

theorem rebalance_branch (before after : List Q)
    (hb : ∀ q ∈ before, Canonical q) (ha : ∀ q ∈ after, Canonical q) :
    decide (foldQ (rebalanceQ before after) zero≠zero)=false := by
  rw [rebalance_audit before after hb ha]
  rfl
#print axioms rebalance_branch
end PV_L2C_QBalance
