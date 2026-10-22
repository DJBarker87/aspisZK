import OraclePortS10CFG

/-! Symbolic CFG cut facts for fn batch_merkle_values.
Exact graph extraction is hash-pinned in cfg.json; Rust execution and
source/model oracle correspondence remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10Dominance0
open OraclePortS10CFG

inductive Edge : Nat → Nat → Prop where
  | e0 : Edge 0 1
  | e1 : Edge 1 2
  | e2 : Edge 1 7
  | e3 : Edge 1 8
  | e4 : Edge 3 2
  | e5 : Edge 3 9
  | e6 : Edge 3 10
  | e7 : Edge 4 2
  | e8 : Edge 4 11
  | e9 : Edge 4 12
  | e10 : Edge 5 6
  | e11 : Edge 7 5
  | e12 : Edge 8 3
  | e13 : Edge 9 5
  | e14 : Edge 10 4
  | e15 : Edge 11 5
  | e16 : Edge 12 6

def mark8 : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | _ => false

theorem closed8 : ∀ x y, Edge x y → y ≠ 8 →
    mark8 x = true → mark8 y = true := by
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
  | e8 => exact by cases marked
  | e9 => exact by cases marked
  | e10 => exact rfl
  | e11 => exact rfl
  | e12 => exact by cases marked
  | e13 => exact rfl
  | e14 => exact by cases marked
  | e15 => exact rfl
  | e16 => exact rfl

#print axioms closed8

theorem fact_0 : Dominates Edge 0 0 8 :=
  root_dominates Edge 0 8

#print axioms fact_0

theorem fact_1 : Dominates Edge 0 0 10 :=
  root_dominates Edge 0 10

#print axioms fact_1

theorem fact_2 : Dominates Edge 0 8 10 :=
  dominates_of_cut mark8 rfl rfl closed8

#print axioms fact_2
end AspisR1.OraclePortS10Dominance0
