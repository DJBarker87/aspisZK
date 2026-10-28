import PV_B3P_RustResult
namespace PV_B3P_HelperEffects224
open Aeneas Aeneas.Std PV_B3P_RustResult
set_option autoImplicit false

-- A compositional specification, pending instantiation with the exact emission.
-- Operations are values supplied as parameters, not asserted native facts.
structure Operations (F W E : Type) where
  zero : F
  active : W → Bool
  sub : F → F → Result F
  inverse : F → Result (Option F)
  weighted : F → W → Result F
  add : F → F → Result F
  imbalance : E

def endpoint {F W E : Type} (ops : Operations F W E) (consumer : Bool)
    (chi value operand : F) (weight : W) : Result (core.result.Result F E) := do
  if ops.active weight then
    let denominator ← ops.sub chi operand
    let inverse ← ops.inverse denominator
    match inverse with
    | none => .ok (.Err ops.imbalance)
    | some inv =>
      let term ← ops.weighted inv weight
      let next ← if consumer then ops.sub value term else ops.add value term
      .ok (.Ok next)
  else .ok (.Ok value)

def slots {F W E : Type} (ops : Operations F W E) (consumer : Bool) (chi value : F) :
    List (F × W) → Result (core.result.Result F E)
  | [] => .ok (.Ok value)
  | (operand,weight)::tail => bindR (endpoint ops consumer chi value operand weight)
      (fun next => slots ops consumer chi next tail)

def row {F W E : Type} (ops : Operations F W E) (chi : F)
    (p0 p1 c0 c1 : F × W) : Result (core.result.Result F E) :=
  bindR (slots ops false chi ops.zero [p0,p1]) (fun value => slots ops true chi value [c0,c1])

theorem inactive {F W E : Type} (ops : Operations F W E) (consumer : Bool)
    (chi value operand : F) (weight : W) (h : ops.active weight = false) :
    endpoint ops consumer chi value operand weight = .ok (.Ok value) := by
  simp only [endpoint,h,Bool.false_eq_true,↓reduceIte]

theorem pole {F W E : Type} (ops : Operations F W E) (consumer : Bool)
    (chi value operand denominator : F) (weight : W)
    (ha : ops.active weight = true) (hd : ops.sub chi operand = .ok denominator)
    (hi : ops.inverse denominator = .ok none) :
    endpoint ops consumer chi value operand weight = .ok (.Err ops.imbalance) := by
  simp only [endpoint,ha,↓reduceIte,hd,hi,bind_tc_ok]

theorem slots_append {F W E : Type} (ops : Operations F W E) (consumer : Bool)
    (chi value : F) (xs ys : List (F × W)) :
    slots ops consumer chi value (xs++ys) =
      bindR (slots ops consumer chi value xs) (fun next => slots ops consumer chi next ys) := by
  induction xs generalizing value with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨operand,weight⟩
    simp only [List.cons_append,slots,bindR_assoc,ih]

theorem two_slots {F W E : Type} (ops : Operations F W E) (consumer : Bool)
    (chi value : F) (a b : F × W) :
    slots ops consumer chi value [a,b] =
      bindR (endpoint ops consumer chi value a.1 a.2) (fun v => endpoint ops consumer chi v b.1 b.2) := by
  rcases a with ⟨a,wa⟩; rcases b with ⟨b,wb⟩
  simp only [slots]
  cases endpoint ops consumer chi value a wa with
  | fail e => rfl
  | div => rfl
  | ok x =>
    cases x with
    | Err e => rfl
    | Ok v =>
      simp only [bindR]
      cases endpoint ops consumer chi v b wb with
      | fail e => rfl
      | div => rfl
      | ok x => cases x <;> rfl

#print axioms inactive
#print axioms pole
#print axioms slots_append
#print axioms two_slots
end PV_B3P_HelperEffects224
