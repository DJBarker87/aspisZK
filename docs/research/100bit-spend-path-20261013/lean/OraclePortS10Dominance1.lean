import OraclePortS10CFG

/-! Symbolic CFG cut facts for fn tx1.
Exact graph extraction is hash-pinned in cfg.json; Rust execution and
source/model oracle correspondence remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10Dominance1
open OraclePortS10CFG

inductive Edge : Nat → Nat → Prop where
  | e0 : Edge 0 1
  | e1 : Edge 0 2
  | e2 : Edge 1 42
  | e3 : Edge 2 3
  | e4 : Edge 3 4
  | e5 : Edge 3 45
  | e6 : Edge 3 46
  | e7 : Edge 5 7
  | e8 : Edge 6 42
  | e9 : Edge 7 4
  | e10 : Edge 7 48
  | e11 : Edge 7 49
  | e12 : Edge 8 10
  | e13 : Edge 9 42
  | e14 : Edge 10 11
  | e15 : Edge 11 4
  | e16 : Edge 11 51
  | e17 : Edge 11 52
  | e18 : Edge 12 14
  | e19 : Edge 13 41
  | e20 : Edge 14 4
  | e21 : Edge 14 54
  | e22 : Edge 14 55
  | e23 : Edge 15 17
  | e24 : Edge 16 40
  | e25 : Edge 17 56
  | e26 : Edge 18 4
  | e27 : Edge 18 63
  | e28 : Edge 18 64
  | e29 : Edge 19 21
  | e30 : Edge 20 39
  | e31 : Edge 21 22
  | e32 : Edge 22 4
  | e33 : Edge 22 66
  | e34 : Edge 22 67
  | e35 : Edge 23 25
  | e36 : Edge 24 38
  | e37 : Edge 25 4
  | e38 : Edge 25 69
  | e39 : Edge 25 70
  | e40 : Edge 26 71
  | e41 : Edge 27 37
  | e42 : Edge 28 30
  | e43 : Edge 29 37
  | e44 : Edge 30 31
  | e45 : Edge 31 32
  | e46 : Edge 32 33
  | e47 : Edge 33 34
  | e48 : Edge 34 35
  | e49 : Edge 35 36
  | e50 : Edge 36 42
  | e51 : Edge 37 38
  | e52 : Edge 38 39
  | e53 : Edge 39 40
  | e54 : Edge 39 43
  | e55 : Edge 40 41
  | e56 : Edge 41 42
  | e57 : Edge 43 40
  | e58 : Edge 44 4
  | e59 : Edge 44 5
  | e60 : Edge 44 6
  | e61 : Edge 45 44
  | e62 : Edge 46 44
  | e63 : Edge 47 4
  | e64 : Edge 47 8
  | e65 : Edge 47 9
  | e66 : Edge 48 47
  | e67 : Edge 49 47
  | e68 : Edge 50 4
  | e69 : Edge 50 12
  | e70 : Edge 50 13
  | e71 : Edge 51 50
  | e72 : Edge 52 50
  | e73 : Edge 53 4
  | e74 : Edge 53 15
  | e75 : Edge 53 16
  | e76 : Edge 54 53
  | e77 : Edge 55 53
  | e78 : Edge 56 57
  | e79 : Edge 56 58
  | e80 : Edge 57 59
  | e81 : Edge 58 59
  | e82 : Edge 59 4
  | e83 : Edge 59 60
  | e84 : Edge 59 61
  | e85 : Edge 61 18
  | e86 : Edge 62 4
  | e87 : Edge 62 19
  | e88 : Edge 62 20
  | e89 : Edge 63 62
  | e90 : Edge 64 62
  | e91 : Edge 65 4
  | e92 : Edge 65 23
  | e93 : Edge 65 24
  | e94 : Edge 66 65
  | e95 : Edge 67 65
  | e96 : Edge 68 4
  | e97 : Edge 68 26
  | e98 : Edge 68 27
  | e99 : Edge 69 68
  | e100 : Edge 70 68
  | e101 : Edge 71 4
  | e102 : Edge 71 72
  | e103 : Edge 71 73
  | e104 : Edge 72 74
  | e105 : Edge 72 75
  | e106 : Edge 73 77
  | e107 : Edge 74 77
  | e108 : Edge 75 76
  | e109 : Edge 76 4
  | e110 : Edge 76 78
  | e111 : Edge 77 4
  | e112 : Edge 77 79
  | e113 : Edge 78 71
  | e114 : Edge 79 4
  | e115 : Edge 79 81
  | e116 : Edge 79 82
  | e117 : Edge 80 4
  | e118 : Edge 80 28
  | e119 : Edge 80 29
  | e120 : Edge 81 80
  | e121 : Edge 82 80

def mark2 : Nat → Bool
  | 0 => true
  | 1 => true
  | 42 => true
  | _ => false

theorem closed2 : ∀ x y, Edge x y → y ≠ 2 →
    mark2 x = true → mark2 y = true := by
  intro x y edge different marked
  cases edge with
  | e0 => exact rfl
  | e1 => exact False.elim (different rfl)
  | e2 => exact rfl
  | e3 => exact by cases marked
  | e4 => exact by cases marked
  | e5 => exact by cases marked
  | e6 => exact by cases marked
  | e7 => exact by cases marked
  | e8 => exact rfl
  | e9 => exact by cases marked
  | e10 => exact by cases marked
  | e11 => exact by cases marked
  | e12 => exact by cases marked
  | e13 => exact rfl
  | e14 => exact by cases marked
  | e15 => exact by cases marked
  | e16 => exact by cases marked
  | e17 => exact by cases marked
  | e18 => exact by cases marked
  | e19 => exact by cases marked
  | e20 => exact by cases marked
  | e21 => exact by cases marked
  | e22 => exact by cases marked
  | e23 => exact by cases marked
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
  | e35 => exact by cases marked
  | e36 => exact by cases marked
  | e37 => exact by cases marked
  | e38 => exact by cases marked
  | e39 => exact by cases marked
  | e40 => exact by cases marked
  | e41 => exact by cases marked
  | e42 => exact by cases marked
  | e43 => exact by cases marked
  | e44 => exact by cases marked
  | e45 => exact by cases marked
  | e46 => exact by cases marked
  | e47 => exact by cases marked
  | e48 => exact by cases marked
  | e49 => exact by cases marked
  | e50 => exact rfl
  | e51 => exact by cases marked
  | e52 => exact by cases marked
  | e53 => exact by cases marked
  | e54 => exact by cases marked
  | e55 => exact by cases marked
  | e56 => exact rfl
  | e57 => exact by cases marked
  | e58 => exact by cases marked
  | e59 => exact by cases marked
  | e60 => exact by cases marked
  | e61 => exact by cases marked
  | e62 => exact by cases marked
  | e63 => exact by cases marked
  | e64 => exact by cases marked
  | e65 => exact by cases marked
  | e66 => exact by cases marked
  | e67 => exact by cases marked
  | e68 => exact by cases marked
  | e69 => exact by cases marked
  | e70 => exact by cases marked
  | e71 => exact by cases marked
  | e72 => exact by cases marked
  | e73 => exact by cases marked
  | e74 => exact by cases marked
  | e75 => exact by cases marked
  | e76 => exact by cases marked
  | e77 => exact by cases marked
  | e78 => exact by cases marked
  | e79 => exact by cases marked
  | e80 => exact by cases marked
  | e81 => exact by cases marked
  | e82 => exact by cases marked
  | e83 => exact by cases marked
  | e84 => exact by cases marked
  | e85 => exact by cases marked
  | e86 => exact by cases marked
  | e87 => exact by cases marked
  | e88 => exact by cases marked
  | e89 => exact by cases marked
  | e90 => exact by cases marked
  | e91 => exact by cases marked
  | e92 => exact by cases marked
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact by cases marked
  | e96 => exact by cases marked
  | e97 => exact by cases marked
  | e98 => exact by cases marked
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact by cases marked
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked
  | e106 => exact by cases marked
  | e107 => exact by cases marked
  | e108 => exact by cases marked
  | e109 => exact by cases marked
  | e110 => exact by cases marked
  | e111 => exact by cases marked
  | e112 => exact by cases marked
  | e113 => exact by cases marked
  | e114 => exact by cases marked
  | e115 => exact by cases marked
  | e116 => exact by cases marked
  | e117 => exact by cases marked
  | e118 => exact by cases marked
  | e119 => exact by cases marked
  | e120 => exact by cases marked
  | e121 => exact by cases marked

#print axioms closed2

def mark5 : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 6 => true
  | 42 => true
  | 44 => true
  | 45 => true
  | 46 => true
  | _ => false

theorem closed5 : ∀ x y, Edge x y → y ≠ 5 →
    mark5 x = true → mark5 y = true := by
  intro x y edge different marked
  cases edge with
  | e0 => exact rfl
  | e1 => exact rfl
  | e2 => exact rfl
  | e3 => exact rfl
  | e4 => exact rfl
  | e5 => exact rfl
  | e6 => exact rfl
  | e7 => exact by cases marked
  | e8 => exact rfl
  | e9 => exact rfl
  | e10 => exact by cases marked
  | e11 => exact by cases marked
  | e12 => exact by cases marked
  | e13 => exact rfl
  | e14 => exact by cases marked
  | e15 => exact rfl
  | e16 => exact by cases marked
  | e17 => exact by cases marked
  | e18 => exact by cases marked
  | e19 => exact by cases marked
  | e20 => exact rfl
  | e21 => exact by cases marked
  | e22 => exact by cases marked
  | e23 => exact by cases marked
  | e24 => exact by cases marked
  | e25 => exact by cases marked
  | e26 => exact rfl
  | e27 => exact by cases marked
  | e28 => exact by cases marked
  | e29 => exact by cases marked
  | e30 => exact by cases marked
  | e31 => exact by cases marked
  | e32 => exact rfl
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact by cases marked
  | e36 => exact by cases marked
  | e37 => exact rfl
  | e38 => exact by cases marked
  | e39 => exact by cases marked
  | e40 => exact by cases marked
  | e41 => exact by cases marked
  | e42 => exact by cases marked
  | e43 => exact by cases marked
  | e44 => exact by cases marked
  | e45 => exact by cases marked
  | e46 => exact by cases marked
  | e47 => exact by cases marked
  | e48 => exact by cases marked
  | e49 => exact by cases marked
  | e50 => exact rfl
  | e51 => exact by cases marked
  | e52 => exact by cases marked
  | e53 => exact by cases marked
  | e54 => exact by cases marked
  | e55 => exact by cases marked
  | e56 => exact rfl
  | e57 => exact by cases marked
  | e58 => exact rfl
  | e59 => exact False.elim (different rfl)
  | e60 => exact rfl
  | e61 => exact rfl
  | e62 => exact rfl
  | e63 => exact rfl
  | e64 => exact by cases marked
  | e65 => exact by cases marked
  | e66 => exact by cases marked
  | e67 => exact by cases marked
  | e68 => exact rfl
  | e69 => exact by cases marked
  | e70 => exact by cases marked
  | e71 => exact by cases marked
  | e72 => exact by cases marked
  | e73 => exact rfl
  | e74 => exact by cases marked
  | e75 => exact by cases marked
  | e76 => exact by cases marked
  | e77 => exact by cases marked
  | e78 => exact by cases marked
  | e79 => exact by cases marked
  | e80 => exact by cases marked
  | e81 => exact by cases marked
  | e82 => exact rfl
  | e83 => exact by cases marked
  | e84 => exact by cases marked
  | e85 => exact by cases marked
  | e86 => exact rfl
  | e87 => exact by cases marked
  | e88 => exact by cases marked
  | e89 => exact by cases marked
  | e90 => exact by cases marked
  | e91 => exact rfl
  | e92 => exact by cases marked
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact by cases marked
  | e96 => exact rfl
  | e97 => exact by cases marked
  | e98 => exact by cases marked
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact rfl
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked
  | e106 => exact by cases marked
  | e107 => exact by cases marked
  | e108 => exact by cases marked
  | e109 => exact rfl
  | e110 => exact by cases marked
  | e111 => exact rfl
  | e112 => exact by cases marked
  | e113 => exact by cases marked
  | e114 => exact rfl
  | e115 => exact by cases marked
  | e116 => exact by cases marked
  | e117 => exact rfl
  | e118 => exact by cases marked
  | e119 => exact by cases marked
  | e120 => exact by cases marked
  | e121 => exact by cases marked

#print axioms closed5

def mark10 : Nat → Bool
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
  | 42 => true
  | 44 => true
  | 45 => true
  | 46 => true
  | 47 => true
  | 48 => true
  | 49 => true
  | _ => false

theorem closed10 : ∀ x y, Edge x y → y ≠ 10 →
    mark10 x = true → mark10 y = true := by
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
  | e12 => exact False.elim (different rfl)
  | e13 => exact rfl
  | e14 => exact by cases marked
  | e15 => exact rfl
  | e16 => exact by cases marked
  | e17 => exact by cases marked
  | e18 => exact by cases marked
  | e19 => exact by cases marked
  | e20 => exact rfl
  | e21 => exact by cases marked
  | e22 => exact by cases marked
  | e23 => exact by cases marked
  | e24 => exact by cases marked
  | e25 => exact by cases marked
  | e26 => exact rfl
  | e27 => exact by cases marked
  | e28 => exact by cases marked
  | e29 => exact by cases marked
  | e30 => exact by cases marked
  | e31 => exact by cases marked
  | e32 => exact rfl
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact by cases marked
  | e36 => exact by cases marked
  | e37 => exact rfl
  | e38 => exact by cases marked
  | e39 => exact by cases marked
  | e40 => exact by cases marked
  | e41 => exact by cases marked
  | e42 => exact by cases marked
  | e43 => exact by cases marked
  | e44 => exact by cases marked
  | e45 => exact by cases marked
  | e46 => exact by cases marked
  | e47 => exact by cases marked
  | e48 => exact by cases marked
  | e49 => exact by cases marked
  | e50 => exact rfl
  | e51 => exact by cases marked
  | e52 => exact by cases marked
  | e53 => exact by cases marked
  | e54 => exact by cases marked
  | e55 => exact by cases marked
  | e56 => exact rfl
  | e57 => exact by cases marked
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
  | e69 => exact by cases marked
  | e70 => exact by cases marked
  | e71 => exact by cases marked
  | e72 => exact by cases marked
  | e73 => exact rfl
  | e74 => exact by cases marked
  | e75 => exact by cases marked
  | e76 => exact by cases marked
  | e77 => exact by cases marked
  | e78 => exact by cases marked
  | e79 => exact by cases marked
  | e80 => exact by cases marked
  | e81 => exact by cases marked
  | e82 => exact rfl
  | e83 => exact by cases marked
  | e84 => exact by cases marked
  | e85 => exact by cases marked
  | e86 => exact rfl
  | e87 => exact by cases marked
  | e88 => exact by cases marked
  | e89 => exact by cases marked
  | e90 => exact by cases marked
  | e91 => exact rfl
  | e92 => exact by cases marked
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact by cases marked
  | e96 => exact rfl
  | e97 => exact by cases marked
  | e98 => exact by cases marked
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact rfl
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked
  | e106 => exact by cases marked
  | e107 => exact by cases marked
  | e108 => exact by cases marked
  | e109 => exact rfl
  | e110 => exact by cases marked
  | e111 => exact rfl
  | e112 => exact by cases marked
  | e113 => exact by cases marked
  | e114 => exact rfl
  | e115 => exact by cases marked
  | e116 => exact by cases marked
  | e117 => exact rfl
  | e118 => exact by cases marked
  | e119 => exact by cases marked
  | e120 => exact by cases marked
  | e121 => exact by cases marked

#print axioms closed10

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
  | 13 => true
  | 41 => true
  | 42 => true
  | 44 => true
  | 45 => true
  | 46 => true
  | 47 => true
  | 48 => true
  | 49 => true
  | 50 => true
  | 51 => true
  | 52 => true
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
  | e15 => exact rfl
  | e16 => exact rfl
  | e17 => exact rfl
  | e18 => exact by cases marked
  | e19 => exact rfl
  | e20 => exact rfl
  | e21 => exact by cases marked
  | e22 => exact by cases marked
  | e23 => exact by cases marked
  | e24 => exact by cases marked
  | e25 => exact by cases marked
  | e26 => exact rfl
  | e27 => exact by cases marked
  | e28 => exact by cases marked
  | e29 => exact by cases marked
  | e30 => exact by cases marked
  | e31 => exact by cases marked
  | e32 => exact rfl
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact by cases marked
  | e36 => exact by cases marked
  | e37 => exact rfl
  | e38 => exact by cases marked
  | e39 => exact by cases marked
  | e40 => exact by cases marked
  | e41 => exact by cases marked
  | e42 => exact by cases marked
  | e43 => exact by cases marked
  | e44 => exact by cases marked
  | e45 => exact by cases marked
  | e46 => exact by cases marked
  | e47 => exact by cases marked
  | e48 => exact by cases marked
  | e49 => exact by cases marked
  | e50 => exact rfl
  | e51 => exact by cases marked
  | e52 => exact by cases marked
  | e53 => exact by cases marked
  | e54 => exact by cases marked
  | e55 => exact rfl
  | e56 => exact rfl
  | e57 => exact by cases marked
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
  | e69 => exact False.elim (different rfl)
  | e70 => exact rfl
  | e71 => exact rfl
  | e72 => exact rfl
  | e73 => exact rfl
  | e74 => exact by cases marked
  | e75 => exact by cases marked
  | e76 => exact by cases marked
  | e77 => exact by cases marked
  | e78 => exact by cases marked
  | e79 => exact by cases marked
  | e80 => exact by cases marked
  | e81 => exact by cases marked
  | e82 => exact rfl
  | e83 => exact by cases marked
  | e84 => exact by cases marked
  | e85 => exact by cases marked
  | e86 => exact rfl
  | e87 => exact by cases marked
  | e88 => exact by cases marked
  | e89 => exact by cases marked
  | e90 => exact by cases marked
  | e91 => exact rfl
  | e92 => exact by cases marked
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact by cases marked
  | e96 => exact rfl
  | e97 => exact by cases marked
  | e98 => exact by cases marked
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact rfl
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked
  | e106 => exact by cases marked
  | e107 => exact by cases marked
  | e108 => exact by cases marked
  | e109 => exact rfl
  | e110 => exact by cases marked
  | e111 => exact rfl
  | e112 => exact by cases marked
  | e113 => exact by cases marked
  | e114 => exact rfl
  | e115 => exact by cases marked
  | e116 => exact by cases marked
  | e117 => exact rfl
  | e118 => exact by cases marked
  | e119 => exact by cases marked
  | e120 => exact by cases marked
  | e121 => exact by cases marked

#print axioms closed12

def mark21 : Nat → Bool
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
  | 19 => true
  | 20 => true
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
  | _ => false

theorem closed21 : ∀ x y, Edge x y → y ≠ 21 →
    mark21 x = true → mark21 y = true := by
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
  | e28 => exact rfl
  | e29 => exact False.elim (different rfl)
  | e30 => exact rfl
  | e31 => exact by cases marked
  | e32 => exact rfl
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact by cases marked
  | e36 => exact by cases marked
  | e37 => exact rfl
  | e38 => exact by cases marked
  | e39 => exact by cases marked
  | e40 => exact by cases marked
  | e41 => exact by cases marked
  | e42 => exact by cases marked
  | e43 => exact by cases marked
  | e44 => exact by cases marked
  | e45 => exact by cases marked
  | e46 => exact by cases marked
  | e47 => exact by cases marked
  | e48 => exact by cases marked
  | e49 => exact by cases marked
  | e50 => exact rfl
  | e51 => exact by cases marked
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
  | e92 => exact by cases marked
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact by cases marked
  | e96 => exact rfl
  | e97 => exact by cases marked
  | e98 => exact by cases marked
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact rfl
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked
  | e106 => exact by cases marked
  | e107 => exact by cases marked
  | e108 => exact by cases marked
  | e109 => exact rfl
  | e110 => exact by cases marked
  | e111 => exact rfl
  | e112 => exact by cases marked
  | e113 => exact by cases marked
  | e114 => exact rfl
  | e115 => exact by cases marked
  | e116 => exact by cases marked
  | e117 => exact rfl
  | e118 => exact by cases marked
  | e119 => exact by cases marked
  | e120 => exact by cases marked
  | e121 => exact by cases marked

#print axioms closed21

def mark23 : Nat → Bool
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
  | 19 => true
  | 20 => true
  | 21 => true
  | 22 => true
  | 24 => true
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
  | _ => false

theorem closed23 : ∀ x y, Edge x y → y ≠ 23 →
    mark23 x = true → mark23 y = true := by
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
  | e28 => exact rfl
  | e29 => exact rfl
  | e30 => exact rfl
  | e31 => exact rfl
  | e32 => exact rfl
  | e33 => exact rfl
  | e34 => exact rfl
  | e35 => exact by cases marked
  | e36 => exact rfl
  | e37 => exact rfl
  | e38 => exact by cases marked
  | e39 => exact by cases marked
  | e40 => exact by cases marked
  | e41 => exact by cases marked
  | e42 => exact by cases marked
  | e43 => exact by cases marked
  | e44 => exact by cases marked
  | e45 => exact by cases marked
  | e46 => exact by cases marked
  | e47 => exact by cases marked
  | e48 => exact by cases marked
  | e49 => exact by cases marked
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
  | e92 => exact False.elim (different rfl)
  | e93 => exact rfl
  | e94 => exact rfl
  | e95 => exact rfl
  | e96 => exact rfl
  | e97 => exact by cases marked
  | e98 => exact by cases marked
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact rfl
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked
  | e106 => exact by cases marked
  | e107 => exact by cases marked
  | e108 => exact by cases marked
  | e109 => exact rfl
  | e110 => exact by cases marked
  | e111 => exact rfl
  | e112 => exact by cases marked
  | e113 => exact by cases marked
  | e114 => exact rfl
  | e115 => exact by cases marked
  | e116 => exact by cases marked
  | e117 => exact rfl
  | e118 => exact by cases marked
  | e119 => exact by cases marked
  | e120 => exact by cases marked
  | e121 => exact by cases marked

#print axioms closed23

def mark28 : Nat → Bool
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
  | 19 => true
  | 20 => true
  | 21 => true
  | 22 => true
  | 23 => true
  | 24 => true
  | 25 => true
  | 26 => true
  | 27 => true
  | 29 => true
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
  | 72 => true
  | 73 => true
  | 74 => true
  | 75 => true
  | 76 => true
  | 77 => true
  | 78 => true
  | 79 => true
  | 80 => true
  | 81 => true
  | 82 => true
  | _ => false

theorem closed28 : ∀ x y, Edge x y → y ≠ 28 →
    mark28 x = true → mark28 y = true := by
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
  | e28 => exact rfl
  | e29 => exact rfl
  | e30 => exact rfl
  | e31 => exact rfl
  | e32 => exact rfl
  | e33 => exact rfl
  | e34 => exact rfl
  | e35 => exact rfl
  | e36 => exact rfl
  | e37 => exact rfl
  | e38 => exact rfl
  | e39 => exact rfl
  | e40 => exact rfl
  | e41 => exact rfl
  | e42 => exact by cases marked
  | e43 => exact rfl
  | e44 => exact by cases marked
  | e45 => exact by cases marked
  | e46 => exact by cases marked
  | e47 => exact by cases marked
  | e48 => exact by cases marked
  | e49 => exact by cases marked
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
  | e99 => exact rfl
  | e100 => exact rfl
  | e101 => exact rfl
  | e102 => exact rfl
  | e103 => exact rfl
  | e104 => exact rfl
  | e105 => exact rfl
  | e106 => exact rfl
  | e107 => exact rfl
  | e108 => exact rfl
  | e109 => exact rfl
  | e110 => exact rfl
  | e111 => exact rfl
  | e112 => exact rfl
  | e113 => exact rfl
  | e114 => exact rfl
  | e115 => exact rfl
  | e116 => exact rfl
  | e117 => exact rfl
  | e118 => exact False.elim (different rfl)
  | e119 => exact rfl
  | e120 => exact rfl
  | e121 => exact rfl

#print axioms closed28

def mark61 : Nat → Bool
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
  | 40 => true
  | 41 => true
  | 42 => true
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
  | _ => false

theorem closed61 : ∀ x y, Edge x y → y ≠ 61 →
    mark61 x = true → mark61 y = true := by
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
  | e27 => exact by cases marked
  | e28 => exact by cases marked
  | e29 => exact by cases marked
  | e30 => exact by cases marked
  | e31 => exact by cases marked
  | e32 => exact rfl
  | e33 => exact by cases marked
  | e34 => exact by cases marked
  | e35 => exact by cases marked
  | e36 => exact by cases marked
  | e37 => exact rfl
  | e38 => exact by cases marked
  | e39 => exact by cases marked
  | e40 => exact by cases marked
  | e41 => exact by cases marked
  | e42 => exact by cases marked
  | e43 => exact by cases marked
  | e44 => exact by cases marked
  | e45 => exact by cases marked
  | e46 => exact by cases marked
  | e47 => exact by cases marked
  | e48 => exact by cases marked
  | e49 => exact by cases marked
  | e50 => exact rfl
  | e51 => exact by cases marked
  | e52 => exact by cases marked
  | e53 => exact rfl
  | e54 => exact by cases marked
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
  | e84 => exact False.elim (different rfl)
  | e85 => exact by cases marked
  | e86 => exact rfl
  | e87 => exact by cases marked
  | e88 => exact by cases marked
  | e89 => exact by cases marked
  | e90 => exact by cases marked
  | e91 => exact rfl
  | e92 => exact by cases marked
  | e93 => exact by cases marked
  | e94 => exact by cases marked
  | e95 => exact by cases marked
  | e96 => exact rfl
  | e97 => exact by cases marked
  | e98 => exact by cases marked
  | e99 => exact by cases marked
  | e100 => exact by cases marked
  | e101 => exact rfl
  | e102 => exact by cases marked
  | e103 => exact by cases marked
  | e104 => exact by cases marked
  | e105 => exact by cases marked
  | e106 => exact by cases marked
  | e107 => exact by cases marked
  | e108 => exact by cases marked
  | e109 => exact rfl
  | e110 => exact by cases marked
  | e111 => exact rfl
  | e112 => exact by cases marked
  | e113 => exact by cases marked
  | e114 => exact rfl
  | e115 => exact by cases marked
  | e116 => exact by cases marked
  | e117 => exact rfl
  | e118 => exact by cases marked
  | e119 => exact by cases marked
  | e120 => exact by cases marked
  | e121 => exact by cases marked

#print axioms closed61

theorem fact_0 : Dominates Edge 0 2 5 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_0

theorem fact_1 : Dominates Edge 0 2 10 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_1

theorem fact_2 : Dominates Edge 0 2 12 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_2

theorem fact_3 : Dominates Edge 0 2 21 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_3

theorem fact_4 : Dominates Edge 0 2 23 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_4

theorem fact_5 : Dominates Edge 0 2 28 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_5

theorem fact_6 : Dominates Edge 0 2 30 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_6

theorem fact_7 : Dominates Edge 0 2 61 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_7

theorem fact_8 : Dominates Edge 0 2 75 :=
  dominates_of_cut mark2 rfl rfl closed2

#print axioms fact_8

theorem fact_9 : Dominates Edge 0 5 10 :=
  dominates_of_cut mark5 rfl rfl closed5

#print axioms fact_9

theorem fact_10 : Dominates Edge 0 5 12 :=
  dominates_of_cut mark5 rfl rfl closed5

#print axioms fact_10

theorem fact_11 : Dominates Edge 0 5 21 :=
  dominates_of_cut mark5 rfl rfl closed5

#print axioms fact_11

theorem fact_12 : Dominates Edge 0 5 23 :=
  dominates_of_cut mark5 rfl rfl closed5

#print axioms fact_12

theorem fact_13 : Dominates Edge 0 5 28 :=
  dominates_of_cut mark5 rfl rfl closed5

#print axioms fact_13

theorem fact_14 : Dominates Edge 0 5 30 :=
  dominates_of_cut mark5 rfl rfl closed5

#print axioms fact_14

theorem fact_15 : Dominates Edge 0 5 61 :=
  dominates_of_cut mark5 rfl rfl closed5

#print axioms fact_15

theorem fact_16 : Dominates Edge 0 5 75 :=
  dominates_of_cut mark5 rfl rfl closed5

#print axioms fact_16

theorem fact_17 : Dominates Edge 0 10 12 :=
  dominates_of_cut mark10 rfl rfl closed10

#print axioms fact_17

theorem fact_18 : Dominates Edge 0 10 21 :=
  dominates_of_cut mark10 rfl rfl closed10

#print axioms fact_18

theorem fact_19 : Dominates Edge 0 10 23 :=
  dominates_of_cut mark10 rfl rfl closed10

#print axioms fact_19

theorem fact_20 : Dominates Edge 0 10 28 :=
  dominates_of_cut mark10 rfl rfl closed10

#print axioms fact_20

theorem fact_21 : Dominates Edge 0 10 30 :=
  dominates_of_cut mark10 rfl rfl closed10

#print axioms fact_21

theorem fact_22 : Dominates Edge 0 10 61 :=
  dominates_of_cut mark10 rfl rfl closed10

#print axioms fact_22

theorem fact_23 : Dominates Edge 0 10 75 :=
  dominates_of_cut mark10 rfl rfl closed10

#print axioms fact_23

theorem fact_24 : Dominates Edge 0 12 21 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_24

theorem fact_25 : Dominates Edge 0 12 23 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_25

theorem fact_26 : Dominates Edge 0 12 28 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_26

theorem fact_27 : Dominates Edge 0 12 30 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_27

theorem fact_28 : Dominates Edge 0 12 61 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_28

theorem fact_29 : Dominates Edge 0 12 75 :=
  dominates_of_cut mark12 rfl rfl closed12

#print axioms fact_29

theorem fact_30 : Dominates Edge 0 21 23 :=
  dominates_of_cut mark21 rfl rfl closed21

#print axioms fact_30

theorem fact_31 : Dominates Edge 0 21 28 :=
  dominates_of_cut mark21 rfl rfl closed21

#print axioms fact_31

theorem fact_32 : Dominates Edge 0 21 30 :=
  dominates_of_cut mark21 rfl rfl closed21

#print axioms fact_32

theorem fact_33 : Dominates Edge 0 21 75 :=
  dominates_of_cut mark21 rfl rfl closed21

#print axioms fact_33

theorem fact_34 : Dominates Edge 0 23 28 :=
  dominates_of_cut mark23 rfl rfl closed23

#print axioms fact_34

theorem fact_35 : Dominates Edge 0 23 30 :=
  dominates_of_cut mark23 rfl rfl closed23

#print axioms fact_35

theorem fact_36 : Dominates Edge 0 23 75 :=
  dominates_of_cut mark23 rfl rfl closed23

#print axioms fact_36

theorem fact_37 : Dominates Edge 0 28 30 :=
  dominates_of_cut mark28 rfl rfl closed28

#print axioms fact_37

theorem fact_38 : Dominates Edge 0 61 21 :=
  dominates_of_cut mark61 rfl rfl closed61

#print axioms fact_38

theorem fact_39 : Dominates Edge 0 61 23 :=
  dominates_of_cut mark61 rfl rfl closed61

#print axioms fact_39

theorem fact_40 : Dominates Edge 0 61 28 :=
  dominates_of_cut mark61 rfl rfl closed61

#print axioms fact_40

theorem fact_41 : Dominates Edge 0 61 30 :=
  dominates_of_cut mark61 rfl rfl closed61

#print axioms fact_41

theorem fact_42 : Dominates Edge 0 61 75 :=
  dominates_of_cut mark61 rfl rfl closed61

#print axioms fact_42
end AspisR1.OraclePortS10Dominance1
