import S2LibraFactoredIdentity

set_option autoImplicit false
namespace AspisR1.S9SourceSideUpdatesRootV1
open AspisR1.S2LibraFactoredIdentity
variable {E : Type} [CommSemiring E]

/-- Multiplications and squares in the order used by the frozen helper.
The input q2 is the square supplied by the four-entry kpowers array. -/
structure HighPowers (E : Type) where
  q4 : E
  q8 : E
  q12 : E
  q16 : E

def highPowers (q2 : E) : HighPowers E :=
  let q4 := q2 * q2
  let q8 := q4 * q4
  let q12 := q8 * q4
  let q16 := q8 * q8
  ⟨q4, q8, q12, q16⟩

def highAt (h : HighPowers E) (r : Fin 4) : E :=
  if r.val = 0 then 1 else if r.val = 1 then h.q4
  else if r.val = 2 then h.q8 else h.q12

def terms (p : Fin 4 → E) (quarter : E) (h : HighPowers E) (r : Fin 4) : E :=
  (p (perm r) * highAt h r) * quarter

def sumTwo (t : Fin 4 → E) : E := t 0 + t 1

def sumThree (t : Fin 4 → E) : E := sumTwo t + t 2

def sumFour (t : Fin 4 → E) : E := sumThree t + t 3

/-- First branch preserves the cells it has not written. -/
def sideZero (old : Fin 4 → E) (low : E) (t : Fin 4 → E)
    (q16 : E) (j : Fin 4) : E :=
  if j.val = 0 then low * sumFour t
  else if j.val = 1 then (low * sumThree t) * q16 else old j

/-- Second branch consumes the first branch's cell 1 and overwrites 2 and 3. -/
def sideOne (old : Fin 4 → E) (low : E) (t : Fin 4 → E)
    (last q4 q16 : E) (j : Fin 4) : E :=
  if j.val = 0 then old j
  else if j.val = 1 then old j + low * last
  else if j.val = 2 then (low * sumFour t) * q4
  else (low * sumTwo t) * (q16 * q4)

theorem highPowers_exact (q : E) :
    highPowers (q^2) = ⟨q^4, q^8, q^12, q^16⟩ := by
  apply HighPowers.mk.injEq.mpr
  dsimp [highPowers]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem terms_exact (p : Fin 4 → E) (quarter q : E) (r : Fin 4) :
    terms p quarter (highPowers (q^2)) r =
      scaled p quarter r * q^(4*r.val) := by
  rw [highPowers_exact]
  fin_cases r <;> norm_num [terms, highAt, scaled] <;> ring

theorem sums_exact (p : Fin 4 → E) (quarter q : E) :
    sumTwo (terms p quarter (highPowers (q^2))) =
        firstTwo (scaled p quarter) q ∧
    sumThree (terms p quarter (highPowers (q^2))) =
        firstThree (scaled p quarter) q ∧
    sumFour (terms p quarter (highPowers (q^2))) =
        allFour (scaled p quarter) q := by
  simp only [sumFour, sumThree, sumTwo, terms_exact]
  norm_num [firstTwo, firstThree, allFour]

/-- The complete two-side write schedule returns all four factored weights,
independently of every old output cell. Zero challenges are included. This
is decoded algebra for the actual schedule, not a Rust/library refinement. -/
theorem two_side_updates_eq_factored
    (old p0 p1 : Fin 4 → E) (quarter q0 q1 : E) (j : Fin 4) :
    sideOne
      (sideZero old (scalar (scaled p0 quarter) q0)
        (terms p1 quarter (highPowers (q0^2))) (highPowers (q0^2)).q16)
      (scalar (scaled p0 quarter) q1)
      (terms p1 quarter (highPowers (q1^2)))
      (p1 (perm 3) * quarter)
      (highPowers (q1^2)).q4 (highPowers (q1^2)).q16 j =
    factored (scaled p0 quarter) (scaled p1 quarter) q0 q1 j := by
  obtain ⟨h20, h30, h40⟩ := sums_exact p1 quarter q0
  obtain ⟨h21, h31, h41⟩ := sums_exact p1 quarter q1
  rw [highPowers_exact, highPowers_exact]
  fin_cases j <;>
    simp only [sideOne, sideZero, Fin.reduceFinMk, Fin.val_zero,
      Fin.val_one, Fin.val_two, Fin.val_three, Nat.reduceEqDiff,
      if_true, if_false, h20, h30, h40, h21, h31, h41,
      factored, scaled] <;> ring

/-- Reuses the existing 56-coefficient identity for the same concrete decoded
inputs and write schedule. This statement adds no helper-success premise. -/
theorem two_side_updates_eq_original
    (old p0 p1 : Fin 4 → E) (quarter q0 q1 : E) (j : Fin 4) :
    sideOne
      (sideZero old (scalar (scaled p0 quarter) q0)
        (terms p1 quarter (highPowers (q0^2))) (highPowers (q0^2)).q16)
      (scalar (scaled p0 quarter) q1)
      (terms p1 quarter (highPowers (q1^2)))
      (p1 (perm 3) * quarter)
      (highPowers (q1^2)).q4 (highPowers (q1^2)).q16 j =
    original (scaled p0 quarter) (scaled p1 quarter) q0 q1 j := by
  rw [two_side_updates_eq_factored]
  exact (original_eq_factored _ _ _ _ _).symm

#print axioms highPowers_exact
#print axioms terms_exact
#print axioms sums_exact
#print axioms two_side_updates_eq_factored
#print axioms two_side_updates_eq_original
end AspisR1.S9SourceSideUpdatesRootV1
