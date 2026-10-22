import OraclePortS10CFG

/-! Symbolic CFG cut facts for fn tx2.
Exact graph extraction is hash-pinned in cfg.json; Rust execution and
source/model oracle correspondence remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10Dominance4
open OraclePortS10CFG

inductive Edge : Nat → Nat → Prop where
  | e0 : Edge 0 1
  | e1 : Edge 1 2
  | e2 : Edge 1 6
  | e3 : Edge 1 7
  | e4 : Edge 3 2
  | e5 : Edge 3 8
  | e6 : Edge 3 9
  | e7 : Edge 4 5
  | e8 : Edge 6 5
  | e9 : Edge 7 3
  | e10 : Edge 8 5
  | e11 : Edge 9 4

def mark7 : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 5 => true
  | 6 => true
  | _ => false

theorem closed7 : ∀ x y, Edge x y → y ≠ 7 →
    mark7 x = true → mark7 y = true := by
  intro x y edge different marked
  cases edge with
  | e0 => exact rfl
  | e1 => exact rfl
  | e2 => exact rfl
  | e3 => exact False.elim (different rfl)
  | e4 => exact rfl
  | e5 => exact by cases marked
  | e6 => exact by cases marked
  | e7 => exact rfl
  | e8 => exact rfl
  | e9 => exact by cases marked
  | e10 => exact rfl
  | e11 => exact by cases marked

#print axioms closed7

theorem fact_0 : Dominates Edge 0 0 4 :=
  root_dominates Edge 0 4

#print axioms fact_0

theorem fact_1 : Dominates Edge 0 0 7 :=
  root_dominates Edge 0 7

#print axioms fact_1

theorem fact_2 : Dominates Edge 0 7 4 :=
  dominates_of_cut mark7 rfl rfl closed7

#print axioms fact_2
end AspisR1.OraclePortS10Dominance4
