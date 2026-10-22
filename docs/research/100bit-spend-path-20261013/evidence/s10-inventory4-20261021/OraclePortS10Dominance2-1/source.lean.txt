import OraclePortS10CFG

/-! Symbolic CFG cut facts for fn tx2_common.
Exact graph extraction is hash-pinned in cfg.json; Rust execution and
source/model oracle correspondence remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10Dominance2
open OraclePortS10CFG

inductive Edge : Nat → Nat → Prop where
  | e0 : Edge 0 1
  | e1 : Edge 1 2
  | e2 : Edge 1 35
  | e3 : Edge 1 36
  | e4 : Edge 3 34
  | e5 : Edge 4 37
  | e6 : Edge 5 38
  | e7 : Edge 6 2
  | e8 : Edge 6 40
  | e9 : Edge 6 41
  | e10 : Edge 7 45
  | e11 : Edge 8 30
  | e12 : Edge 9 2
  | e13 : Edge 9 52
  | e14 : Edge 9 53
  | e15 : Edge 10 12
  | e16 : Edge 11 29
  | e17 : Edge 12 13
  | e18 : Edge 13 2
  | e19 : Edge 13 55
  | e20 : Edge 13 56
  | e21 : Edge 14 16
  | e22 : Edge 15 28
  | e23 : Edge 16 2
  | e24 : Edge 16 58
  | e25 : Edge 16 59
  | e26 : Edge 17 60
  | e27 : Edge 18 27
  | e28 : Edge 19 21
  | e29 : Edge 20 27
  | e30 : Edge 21 72
  | e31 : Edge 22 23
  | e32 : Edge 23 24
  | e33 : Edge 24 25
  | e34 : Edge 25 26
  | e35 : Edge 26 33
  | e36 : Edge 27 28
  | e37 : Edge 28 29
  | e38 : Edge 29 30
  | e39 : Edge 30 31
  | e40 : Edge 30 34
  | e41 : Edge 31 32
  | e42 : Edge 32 33
  | e43 : Edge 34 31
  | e44 : Edge 35 33
  | e45 : Edge 36 3
  | e46 : Edge 36 4
  | e47 : Edge 37 5
  | e48 : Edge 38 6
  | e49 : Edge 39 2
  | e50 : Edge 39 43
  | e51 : Edge 39 44
  | e52 : Edge 40 39
  | e53 : Edge 41 39
  | e54 : Edge 42 2
  | e55 : Edge 42 7
  | e56 : Edge 42 8
  | e57 : Edge 43 42
  | e58 : Edge 44 42
  | e59 : Edge 45 46
  | e60 : Edge 45 47
  | e61 : Edge 46 48
  | e62 : Edge 47 48
  | e63 : Edge 48 2
  | e64 : Edge 48 49
  | e65 : Edge 48 50
  | e66 : Edge 50 9
  | e67 : Edge 51 2
  | e68 : Edge 51 10
  | e69 : Edge 51 11
  | e70 : Edge 52 51
  | e71 : Edge 53 51
  | e72 : Edge 54 2
  | e73 : Edge 54 14
  | e74 : Edge 54 15
  | e75 : Edge 55 54
  | e76 : Edge 56 54
  | e77 : Edge 57 2
  | e78 : Edge 57 17
  | e79 : Edge 57 18
  | e80 : Edge 58 57
  | e81 : Edge 59 57
  | e82 : Edge 60 2
  | e83 : Edge 60 61
  | e84 : Edge 60 62
  | e85 : Edge 61 63
  | e86 : Edge 61 64
  | e87 : Edge 62 66
  | e88 : Edge 63 66
  | e89 : Edge 64 65
  | e90 : Edge 65 2
  | e91 : Edge 65 67
  | e92 : Edge 66 2
  | e93 : Edge 66 68
  | e94 : Edge 67 60
  | e95 : Edge 68 2
  | e96 : Edge 68 70
  | e97 : Edge 68 71
  | e98 : Edge 69 2
  | e99 : Edge 69 19
  | e100 : Edge 69 20
  | e101 : Edge 70 69
  | e102 : Edge 71 69
  | e103 : Edge 72 73
  | e104 : Edge 73 74
  | e105 : Edge 74 22

def mark12 : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | 8 => true
  | 9 => true
  | 10 => true
  | 11 => true
  | 29 => true
  | 30 => true
  | 31 => true
  | 32 => true
  | 33 => true
  | 34 => true
  | 35 => true
  | 36 => true
  | 37 => true
  | 38 => true
  | 39 => true
  | 40 => true
  | 41 => true
  | 42 => true
  | 43 => true
  | 44 => true
  | 45 => true
  | 46 => true
  | 47 => true
  | 48 => true
  | 49 => true
  | 50 => true
  | 51 => true
  | 52 => true
  | 53 => true
  | _ => false

theorem closed12 : ∀ x y, Edge x y → y ≠ 12 →
    mark12 x = true → mark12 y = true := by
  intro x y edge different marked
  cases edge with
  | e0 => exact rfl
  | e1 => exact rfl
  | e2 => exact rfl
  | e3 => exact rfl
  | e4 => exact rfl
  | e5 => exact rfl
  | e6 => exact rfl
  | e7 => exact rfl
  | e8 => exact rfl
  | e9 => exact rfl
  | e10 => exact rfl
  | e11 => exact rfl
  | e12 => exact rfl
  | e13 => exact rfl
  | e14 => exact rfl
  | e15 => exact False.elim (different rfl)
  | e16 => exact rfl
  | e17 => exact by cases marked
  | e18 => exact rfl
  | e19 => exact by cases marked
  | e20 => exact by cases marked
  | e21 => exact by cases marked
  | e22 => exact by cases marked
  | e23 => exact rfl
  | e24 => exact by cases marked
  | e25 => exact by cases marked
  | e26 => exact by cases marked
  | e27 => exact by cases marked
  | e28 => exact by cases marked
  | e29 => exact by cases marked
  | e30 => exact by cases marked
  | e31 => exact by cases marked
  | e32 => exact by cases marked
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact rfl
  | e36 => exact by cases marked
  | e37 => exact rfl
  | e38 => exact rfl
  | e39 => exact rfl
  | e40 => exact rfl
  | e41 => exact rfl
  | e42 => exact rfl
  | e43 => exact rfl
  | e44 => exact rfl
  | e45 => exact rfl
  | e46 => exact rfl
  | e47 => exact rfl
  | e48 => exact rfl
  | e49 => exact rfl
  | e50 => exact rfl
  | e51 => exact rfl
  | e52 => exact rfl
  | e53 => exact rfl
  | e54 => exact rfl
  | e55 => exact rfl
  | e56 => exact rfl
  | e57 => exact rfl
  | e58 => exact rfl
  | e59 => exact rfl
  | e60 => exact rfl
  | e61 => exact rfl
  | e62 => exact rfl
  | e63 => exact rfl
  | e64 => exact rfl
  | e65 => exact rfl
  | e66 => exact rfl
  | e67 => exact rfl
  | e68 => exact rfl
  | e69 => exact rfl
  | e70 => exact rfl
  | e71 => exact rfl
  | e72 => exact rfl
  | e73 => exact by cases marked
  | e74 => exact by cases marked
  | e75 => exact by cases marked
  | e76 => exact by cases marked
  | e77 => exact rfl
  | e78 => exact by cases marked
  | e79 => exact by cases marked
  | e80 => exact by cases marked
  | e81 => exact by cases marked
  | e82 => exact rfl
  | e83 => exact by cases marked
  | e84 => exact by cases marked
  | e85 => exact by cases marked
  | e86 => exact by cases marked
  | e87 => exact by cases marked
  | e88 => exact by cases marked
  | e89 => exact by cases marked
  | e90 => exact rfl
  | e91 => exact by cases marked
  | e92 => exact rfl
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact rfl
  | e96 => exact by cases marked
  | e97 => exact by cases marked
  | e98 => exact rfl
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact by cases marked
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked

#print axioms closed12

def mark14 : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | 8 => true
  | 9 => true
  | 10 => true
  | 11 => true
  | 12 => true
  | 13 => true
  | 15 => true
  | 28 => true
  | 29 => true
  | 30 => true
  | 31 => true
  | 32 => true
  | 33 => true
  | 34 => true
  | 35 => true
  | 36 => true
  | 37 => true
  | 38 => true
  | 39 => true
  | 40 => true
  | 41 => true
  | 42 => true
  | 43 => true
  | 44 => true
  | 45 => true
  | 46 => true
  | 47 => true
  | 48 => true
  | 49 => true
  | 50 => true
  | 51 => true
  | 52 => true
  | 53 => true
  | 54 => true
  | 55 => true
  | 56 => true
  | _ => false

theorem closed14 : ∀ x y, Edge x y → y ≠ 14 →
    mark14 x = true → mark14 y = true := by
  intro x y edge different marked
  cases edge with
  | e0 => exact rfl
  | e1 => exact rfl
  | e2 => exact rfl
  | e3 => exact rfl
  | e4 => exact rfl
  | e5 => exact rfl
  | e6 => exact rfl
  | e7 => exact rfl
  | e8 => exact rfl
  | e9 => exact rfl
  | e10 => exact rfl
  | e11 => exact rfl
  | e12 => exact rfl
  | e13 => exact rfl
  | e14 => exact rfl
  | e15 => exact rfl
  | e16 => exact rfl
  | e17 => exact rfl
  | e18 => exact rfl
  | e19 => exact rfl
  | e20 => exact rfl
  | e21 => exact by cases marked
  | e22 => exact rfl
  | e23 => exact rfl
  | e24 => exact by cases marked
  | e25 => exact by cases marked
  | e26 => exact by cases marked
  | e27 => exact by cases marked
  | e28 => exact by cases marked
  | e29 => exact by cases marked
  | e30 => exact by cases marked
  | e31 => exact by cases marked
  | e32 => exact by cases marked
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact rfl
  | e36 => exact rfl
  | e37 => exact rfl
  | e38 => exact rfl
  | e39 => exact rfl
  | e40 => exact rfl
  | e41 => exact rfl
  | e42 => exact rfl
  | e43 => exact rfl
  | e44 => exact rfl
  | e45 => exact rfl
  | e46 => exact rfl
  | e47 => exact rfl
  | e48 => exact rfl
  | e49 => exact rfl
  | e50 => exact rfl
  | e51 => exact rfl
  | e52 => exact rfl
  | e53 => exact rfl
  | e54 => exact rfl
  | e55 => exact rfl
  | e56 => exact rfl
  | e57 => exact rfl
  | e58 => exact rfl
  | e59 => exact rfl
  | e60 => exact rfl
  | e61 => exact rfl
  | e62 => exact rfl
  | e63 => exact rfl
  | e64 => exact rfl
  | e65 => exact rfl
  | e66 => exact rfl
  | e67 => exact rfl
  | e68 => exact rfl
  | e69 => exact rfl
  | e70 => exact rfl
  | e71 => exact rfl
  | e72 => exact rfl
  | e73 => exact False.elim (different rfl)
  | e74 => exact rfl
  | e75 => exact rfl
  | e76 => exact rfl
  | e77 => exact rfl
  | e78 => exact by cases marked
  | e79 => exact by cases marked
  | e80 => exact by cases marked
  | e81 => exact by cases marked
  | e82 => exact rfl
  | e83 => exact by cases marked
  | e84 => exact by cases marked
  | e85 => exact by cases marked
  | e86 => exact by cases marked
  | e87 => exact by cases marked
  | e88 => exact by cases marked
  | e89 => exact by cases marked
  | e90 => exact rfl
  | e91 => exact by cases marked
  | e92 => exact rfl
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact rfl
  | e96 => exact by cases marked
  | e97 => exact by cases marked
  | e98 => exact rfl
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact by cases marked
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked

#print axioms closed14

def mark19 : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | 8 => true
  | 9 => true
  | 10 => true
  | 11 => true
  | 12 => true
  | 13 => true
  | 14 => true
  | 15 => true
  | 16 => true
  | 17 => true
  | 18 => true
  | 20 => true
  | 27 => true
  | 28 => true
  | 29 => true
  | 30 => true
  | 31 => true
  | 32 => true
  | 33 => true
  | 34 => true
  | 35 => true
  | 36 => true
  | 37 => true
  | 38 => true
  | 39 => true
  | 40 => true
  | 41 => true
  | 42 => true
  | 43 => true
  | 44 => true
  | 45 => true
  | 46 => true
  | 47 => true
  | 48 => true
  | 49 => true
  | 50 => true
  | 51 => true
  | 52 => true
  | 53 => true
  | 54 => true
  | 55 => true
  | 56 => true
  | 57 => true
  | 58 => true
  | 59 => true
  | 60 => true
  | 61 => true
  | 62 => true
  | 63 => true
  | 64 => true
  | 65 => true
  | 66 => true
  | 67 => true
  | 68 => true
  | 69 => true
  | 70 => true
  | 71 => true
  | _ => false

theorem closed19 : ∀ x y, Edge x y → y ≠ 19 →
    mark19 x = true → mark19 y = true := by
  intro x y edge different marked
  cases edge with
  | e0 => exact rfl
  | e1 => exact rfl
  | e2 => exact rfl
  | e3 => exact rfl
  | e4 => exact rfl
  | e5 => exact rfl
  | e6 => exact rfl
  | e7 => exact rfl
  | e8 => exact rfl
  | e9 => exact rfl
  | e10 => exact rfl
  | e11 => exact rfl
  | e12 => exact rfl
  | e13 => exact rfl
  | e14 => exact rfl
  | e15 => exact rfl
  | e16 => exact rfl
  | e17 => exact rfl
  | e18 => exact rfl
  | e19 => exact rfl
  | e20 => exact rfl
  | e21 => exact rfl
  | e22 => exact rfl
  | e23 => exact rfl
  | e24 => exact rfl
  | e25 => exact rfl
  | e26 => exact rfl
  | e27 => exact rfl
  | e28 => exact by cases marked
  | e29 => exact rfl
  | e30 => exact by cases marked
  | e31 => exact by cases marked
  | e32 => exact by cases marked
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact rfl
  | e36 => exact rfl
  | e37 => exact rfl
  | e38 => exact rfl
  | e39 => exact rfl
  | e40 => exact rfl
  | e41 => exact rfl
  | e42 => exact rfl
  | e43 => exact rfl
  | e44 => exact rfl
  | e45 => exact rfl
  | e46 => exact rfl
  | e47 => exact rfl
  | e48 => exact rfl
  | e49 => exact rfl
  | e50 => exact rfl
  | e51 => exact rfl
  | e52 => exact rfl
  | e53 => exact rfl
  | e54 => exact rfl
  | e55 => exact rfl
  | e56 => exact rfl
  | e57 => exact rfl
  | e58 => exact rfl
  | e59 => exact rfl
  | e60 => exact rfl
  | e61 => exact rfl
  | e62 => exact rfl
  | e63 => exact rfl
  | e64 => exact rfl
  | e65 => exact rfl
  | e66 => exact rfl
  | e67 => exact rfl
  | e68 => exact rfl
  | e69 => exact rfl
  | e70 => exact rfl
  | e71 => exact rfl
  | e72 => exact rfl
  | e73 => exact rfl
  | e74 => exact rfl
  | e75 => exact rfl
  | e76 => exact rfl
  | e77 => exact rfl
  | e78 => exact rfl
  | e79 => exact rfl
  | e80 => exact rfl
  | e81 => exact rfl
  | e82 => exact rfl
  | e83 => exact rfl
  | e84 => exact rfl
  | e85 => exact rfl
  | e86 => exact rfl
  | e87 => exact rfl
  | e88 => exact rfl
  | e89 => exact rfl
  | e90 => exact rfl
  | e91 => exact rfl
  | e92 => exact rfl
  | e93 => exact rfl
  | e94 => exact rfl
  | e95 => exact rfl
  | e96 => exact rfl
  | e97 => exact rfl
  | e98 => exact rfl
  | e99 => exact False.elim (different rfl)
  | e100 => exact rfl
  | e101 => exact rfl
  | e102 => exact rfl
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked

#print axioms closed19

def mark50 : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | 8 => true
  | 30 => true
  | 31 => true
  | 32 => true
  | 33 => true
  | 34 => true
  | 35 => true
  | 36 => true
  | 37 => true
  | 38 => true
  | 39 => true
  | 40 => true
  | 41 => true
  | 42 => true
  | 43 => true
  | 44 => true
  | 45 => true
  | 46 => true
  | 47 => true
  | 48 => true
  | 49 => true
  | _ => false

theorem closed50 : ∀ x y, Edge x y → y ≠ 50 →
    mark50 x = true → mark50 y = true := by
  intro x y edge different marked
  cases edge with
  | e0 => exact rfl
  | e1 => exact rfl
  | e2 => exact rfl
  | e3 => exact rfl
  | e4 => exact rfl
  | e5 => exact rfl
  | e6 => exact rfl
  | e7 => exact rfl
  | e8 => exact rfl
  | e9 => exact rfl
  | e10 => exact rfl
  | e11 => exact rfl
  | e12 => exact rfl
  | e13 => exact by cases marked
  | e14 => exact by cases marked
  | e15 => exact by cases marked
  | e16 => exact by cases marked
  | e17 => exact by cases marked
  | e18 => exact rfl
  | e19 => exact by cases marked
  | e20 => exact by cases marked
  | e21 => exact by cases marked
  | e22 => exact by cases marked
  | e23 => exact rfl
  | e24 => exact by cases marked
  | e25 => exact by cases marked
  | e26 => exact by cases marked
  | e27 => exact by cases marked
  | e28 => exact by cases marked
  | e29 => exact by cases marked
  | e30 => exact by cases marked
  | e31 => exact by cases marked
  | e32 => exact by cases marked
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact rfl
  | e36 => exact by cases marked
  | e37 => exact by cases marked
  | e38 => exact rfl
  | e39 => exact rfl
  | e40 => exact rfl
  | e41 => exact rfl
  | e42 => exact rfl
  | e43 => exact rfl
  | e44 => exact rfl
  | e45 => exact rfl
  | e46 => exact rfl
  | e47 => exact rfl
  | e48 => exact rfl
  | e49 => exact rfl
  | e50 => exact rfl
  | e51 => exact rfl
  | e52 => exact rfl
  | e53 => exact rfl
  | e54 => exact rfl
  | e55 => exact rfl
  | e56 => exact rfl
  | e57 => exact rfl
  | e58 => exact rfl
  | e59 => exact rfl
  | e60 => exact rfl
  | e61 => exact rfl
  | e62 => exact rfl
  | e63 => exact rfl
  | e64 => exact rfl
  | e65 => exact False.elim (different rfl)
  | e66 => exact by cases marked
  | e67 => exact rfl
  | e68 => exact by cases marked
  | e69 => exact by cases marked
  | e70 => exact by cases marked
  | e71 => exact by cases marked
  | e72 => exact rfl
  | e73 => exact by cases marked
  | e74 => exact by cases marked
  | e75 => exact by cases marked
  | e76 => exact by cases marked
  | e77 => exact rfl
  | e78 => exact by cases marked
  | e79 => exact by cases marked
  | e80 => exact by cases marked
  | e81 => exact by cases marked
  | e82 => exact rfl
  | e83 => exact by cases marked
  | e84 => exact by cases marked
  | e85 => exact by cases marked
  | e86 => exact by cases marked
  | e87 => exact by cases marked
  | e88 => exact by cases marked
  | e89 => exact by cases marked
  | e90 => exact rfl
  | e91 => exact by cases marked
  | e92 => exact rfl
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact rfl
  | e96 => exact by cases marked
  | e97 => exact by cases marked
  | e98 => exact rfl
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact by cases marked
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked

#print axioms closed50

theorem fact_0 : Dominates Edge 0 0 12 :=
  root_dominates Edge 0 12

#print axioms fact_0

theorem fact_1 : Dominates Edge 0 0 14 :=
  root_dominates Edge 0 14

#print axioms fact_1

theorem fact_2 : Dominates Edge 0 0 19 :=
  root_dominates Edge 0 19

#print axioms fact_2

theorem fact_3 : Dominates Edge 0 0 50 :=
  root_dominates Edge 0 50

#print axioms fact_3

theorem fact_4 : Dominates Edge 0 0 64 :=
  root_dominates Edge 0 64

#print axioms fact_4

theorem fact_5 : Dominates Edge 0 0 74 :=
  root_dominates Edge 0 74

#print axioms fact_5

theorem fact_6 : Dominates Edge 0 12 14 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_6

theorem fact_7 : Dominates Edge 0 12 19 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_7

theorem fact_8 : Dominates Edge 0 12 64 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_8

theorem fact_9 : Dominates Edge 0 12 74 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_9

theorem fact_10 : Dominates Edge 0 14 19 :=
  dominates_of_cut mark14 rfl rfl closed14

#print axioms fact_10

theorem fact_11 : Dominates Edge 0 14 64 :=
  dominates_of_cut mark14 rfl rfl closed14

#print axioms fact_11

theorem fact_12 : Dominates Edge 0 14 74 :=
  dominates_of_cut mark14 rfl rfl closed14

#print axioms fact_12

theorem fact_13 : Dominates Edge 0 19 74 :=
  dominates_of_cut mark19 rfl rfl closed19

#print axioms fact_13

theorem fact_14 : Dominates Edge 0 50 12 :=
  dominates_of_cut mark50 rfl rfl closed50

#print axioms fact_14

theorem fact_15 : Dominates Edge 0 50 14 :=
  dominates_of_cut mark50 rfl rfl closed50

#print axioms fact_15

theorem fact_16 : Dominates Edge 0 50 19 :=
  dominates_of_cut mark50 rfl rfl closed50

#print axioms fact_16

theorem fact_17 : Dominates Edge 0 50 64 :=
  dominates_of_cut mark50 rfl rfl closed50

#print axioms fact_17

theorem fact_18 : Dominates Edge 0 50 74 :=
  dominates_of_cut mark50 rfl rfl closed50

#print axioms fact_18
end AspisR1.OraclePortS10Dominance2
