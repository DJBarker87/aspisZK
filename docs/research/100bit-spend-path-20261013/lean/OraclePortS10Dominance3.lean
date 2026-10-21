import OraclePortS10CFG

/-! Symbolic CFG cut facts for fn tx2_authenticated.
Exact graph extraction is hash-pinned in cfg.json; Rust execution and
source/model oracle correspondence remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10Dominance3
open OraclePortS10CFG

inductive Edge : Nat → Nat → Prop where
  | e0 : Edge 0 1
  | e1 : Edge 1 2
  | e2 : Edge 1 5
  | e3 : Edge 1 6
  | e4 : Edge 3 4
  | e5 : Edge 5 4
  | e6 : Edge 6 3

theorem fact_0 : Dominates Edge 0 0 3 :=
  root_dominates Edge 0 3

#print axioms fact_0
end AspisR1.OraclePortS10Dominance3
