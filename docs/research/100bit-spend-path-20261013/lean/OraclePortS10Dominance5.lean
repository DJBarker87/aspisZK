import OraclePortS10CFG

/-! Symbolic CFG cut facts for fn process_r1_cost_probe_instruction.
Exact graph extraction is hash-pinned in cfg.json; Rust execution and
source/model oracle correspondence remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10Dominance5
open OraclePortS10CFG

inductive Edge : Nat → Nat → Prop where
  | e0 : Edge 0 1
  | e1 : Edge 1 2
  | e2 : Edge 1 3
  | e3 : Edge 2 4
  | e4 : Edge 3 4

theorem fact_0 : Dominates Edge 0 0 2 :=
  root_dominates Edge 0 2

#print axioms fact_0
end AspisR1.OraclePortS10Dominance5
