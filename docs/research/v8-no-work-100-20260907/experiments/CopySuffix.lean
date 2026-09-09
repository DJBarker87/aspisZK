import Mathlib.Tactic

/- Exact source-shaped fourteen-pattern rewrite, over every commutative ring.
   No inverse or nonzero-challenge hypothesis; no honest-opening hypothesis. -/
namespace AspisV8.CopySuffix
variable {K : Type*} [CommRing K]

def weighted (z : K) : List K → K
  | [] => 0
  | a :: as => z * (a + weighted z as)

theorem weighted_append (z : K) (xs ys : List K) :
    weighted z (xs ++ ys) = weighted z xs + z ^ xs.length * weighted z ys := by
  induction xs with
  | nil => simp [weighted]
  | cons a as ih =>
    simp only [List.cons_append, weighted, List.length_cons, ih, pow_succ]
    ring

def cells (x : Fin 16 → K) : List K := List.ofFn x
def slice (x : Fin 16 → K) (start width : Nat) : List K :=
  ((cells x).drop start).take width

def reference (x : Fin 16 → K) (z c : K) : Fin 14 → K := ![
  weighted z (cells x), weighted z (slice x 0 8),
  weighted z (slice x 2 6), weighted z (slice x 0 6),
  weighted z [x 0,x 1], weighted z [x 6,x 7],
  z*x 0,z*x 10,z*x 1,z*x 2,
  weighted z (slice x 8 8) + z^8*c,
  weighted z (slice x 2 8), weighted z (slice x 1 8),
  weighted z (slice x 8 8)]

def suffix (x : Fin 16 → K) (z : K) (j : Nat) := weighted z ((cells x).drop j)
def fast (x : Fin 16 → K) (z c : K) : Fin 14 → K := ![
  suffix x z 0,
  suffix x z 0-z^8*suffix x z 8,
  suffix x z 2-z^6*suffix x z 8,
  suffix x z 0-z^6*suffix x z 6,
  z*x 0+z*(z*x 1), z*(x 6+z*x 7),
  z*x 0,z*x 10,z*x 1,z*x 2,
  suffix x z 8+z^8*c,
  suffix x z 2-z^8*suffix x z 10,
  suffix x z 1-z^8*suffix x z 9,
  suffix x z 8]

theorem take_drop_weighted (xs : List K) (z : K) (n : Nat) (h : n ≤ xs.length) :
    weighted z (xs.take n) = weighted z xs - z^n * weighted z (xs.drop n) := by
  have ha := weighted_append z (xs.take n) (xs.drop n)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left h] at ha
  linear_combination -ha

-- Generic split lemma; independent of the selected sixteen-cell layout.
theorem slice_as_suffix (x : Fin 16 → K) (z : K) (a n : Nat) (h : a+n≤16) :
    weighted z (slice x a n) = suffix x z a-z^n*suffix x z (a+n) := by
  have hh : n ≤ ((cells x).drop a).length := by
    simp only [List.length_drop, cells, List.length_ofFn]
    omega
  have ht := take_drop_weighted ((cells x).drop a) z n hh
  simpa only [slice, suffix, List.drop_drop, Nat.add_comm] using ht

theorem suffix_16 (x : Fin 16 → K) (z : K) : suffix x z 16 = 0 := by
  simp [suffix, cells, weighted]

theorem pattern_equivalence (x : Fin 16 → K) (z c : K) : fast x z c = reference x z c := by
  funext i
  fin_cases i <;> dsimp only [fast, reference]
  -- Only the fixed sixteen-cell layout is expanded here (not a field/domain).
  all_goals simp [suffix, slice, cells, weighted,
    List.ofFn_succ, List.ofFn_zero, pow_succ]
  all_goals ring

theorem powers (z : K) : (z^2)^2*z^2=z^6 ∧ ((z^2)^2)^2=z^8 := by
  constructor <;> ring

#print axioms weighted_append
#print axioms take_drop_weighted
#print axioms slice_as_suffix
#print axioms suffix_16
#print axioms pattern_equivalence
#print axioms powers
end AspisV8.CopySuffix
