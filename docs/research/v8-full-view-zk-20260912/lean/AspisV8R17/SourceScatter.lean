import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

/-! Source-shaped additive scatter loop. Edges are fixed by public indices;
no assumption about challenge randomness enters this linearity result. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F I J : Type*} [CommRing F] [DecidableEq J]

abbrev ScatterEdge (I J F : Type*) := I × J × F

def scatterRun : List (ScatterEdge I J F) → (I → F) → (J → F) → (J → F)
  | [], _, acc => acc
  | (i,j,w)::edges, q, acc =>
      scatterRun edges q (fun r => acc r + if r=j then w*q i else 0)

def scatterValue (edges : List (ScatterEdge I J F)) (q : I → F) (r : J) : F :=
  (edges.map fun e => if r=e.2.1 then e.2.2*q e.1 else 0).sum

theorem scatter_run_value (edges : List (ScatterEdge I J F))
    (q : I → F) (acc : J → F) (r : J) :
    scatterRun edges q acc r = acc r + scatterValue edges q r := by
  induction edges generalizing acc with
  | nil => simp [scatterRun, scatterValue]
  | cons e es ih =>
      rcases e with ⟨i,j,w⟩
      simp only [scatterRun, ih, scatterValue, List.map_cons, List.sum_cons]
      rw [add_assoc]

theorem scatter_value_linear (edges : List (ScatterEdge I J F))
    (q s : I → F) (a b : F) (r : J) :
    scatterValue edges (fun i => a*q i+b*s i) r =
      a*scatterValue edges q r+b*scatterValue edges s r := by
  induction edges with
  | nil => simp [scatterValue]
  | cons e es ih =>
      rcases e with ⟨i,j,w⟩
      simp only [scatterValue, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      by_cases h : r=j <;> simp only [h, ↓reduceIte] <;> ring

def chordEven (x xx : List (ScatterEdge ℕ ℕ F)) (q : ℕ → F)
    (a b c : F) (r : ℕ) : F :=
  a*q (2*r) + b*scatterValue x (fun i => q (2*i)) r +
    c*(q (2*r+1) - scatterValue xx (scatterValue x (fun i => q (2*i+1))) r)

def chordOdd (x : List (ScatterEdge ℕ ℕ F)) (q : ℕ → F)
    (a b c : F) (r : ℕ) : F :=
  c*q (2*r) + a*q (2*r+1) + b*scatterValue x (fun i => q (2*i+1)) r

theorem chordEven_linear (x xx : List (ScatterEdge ℕ ℕ F))
    (q s : ℕ → F) (a b c u v : F) (r : ℕ) :
    chordEven x xx (fun i => u*q i+v*s i) a b c r =
      u*chordEven x xx q a b c r+v*chordEven x xx s a b c r := by
  have hi : scatterValue x (fun i => u*q (2*i+1)+v*s (2*i+1)) =
      (fun r => u*scatterValue x (fun i => q (2*i+1)) r +
        v*scatterValue x (fun i => s (2*i+1)) r) := by
    funext r
    exact scatter_value_linear x (fun i => q (2*i+1)) (fun i => s (2*i+1)) u v r
  unfold chordEven
  rw [hi]
  simp only [scatter_value_linear]
  ring

theorem chordOdd_linear (x : List (ScatterEdge ℕ ℕ F))
    (q s : ℕ → F) (a b c u v : F) (r : ℕ) :
    chordOdd x (fun i => u*q i+v*s i) a b c r =
      u*chordOdd x q a b c r+v*chordOdd x s a b c r := by
  simp only [chordOdd, scatter_value_linear]
  ring

theorem chordEven_components (x xx : List (ScatterEdge ℕ ℕ F))
    (q : ℕ → F) (a b c : F) (r : ℕ) :
    chordEven x xx q a b c r = a*chordEven x xx q 1 0 0 r +
      b*chordEven x xx q 0 1 0 r + c*chordEven x xx q 0 0 1 r := by
  simp [chordEven]

theorem chordOdd_components (x : List (ScatterEdge ℕ ℕ F))
    (q : ℕ → F) (a b c : F) (r : ℕ) :
    chordOdd x q a b c r = a*chordOdd x q 1 0 0 r +
      b*chordOdd x q 0 1 0 r + c*chordOdd x q 0 0 1 r := by
  simp [chordOdd]
  ring

def chordCoefficient (x xx : List (ScatterEdge ℕ ℕ F)) (q : ℕ → F)
    (a b c : F) (r : ℕ) : F :=
  if r%2=0 then chordEven x xx q a b c (r/2) else chordOdd x q a b c (r/2)

theorem chordCoefficient_linear (x xx : List (ScatterEdge ℕ ℕ F))
    (q s : ℕ → F) (a b c u v : F) (r : ℕ) :
    chordCoefficient x xx (fun i => u*q i+v*s i) a b c r =
      u*chordCoefficient x xx q a b c r+v*chordCoefficient x xx s a b c r := by
  unfold chordCoefficient
  split <;> simp only [chordEven_linear, chordOdd_linear]

theorem chordCoefficient_components (x xx : List (ScatterEdge ℕ ℕ F))
    (q : ℕ → F) (a b c : F) (r : ℕ) :
    chordCoefficient x xx q a b c r = a*chordCoefficient x xx q 1 0 0 r +
      b*chordCoefficient x xx q 0 1 0 r + c*chordCoefficient x xx q 0 0 1 r := by
  unfold chordCoefficient
  split
  · exact chordEven_components x xx q a b c (r/2)
  · exact chordOdd_components x q a b c (r/2)

/-- At an active row inverse transport is a fixed coordinate projection.
The arbitrary index here can be its inverse-permutation index. -/
theorem active_source_six_constants (x xx : List (ScatterEdge ℕ ℕ F))
    (q s : ℕ → F) (a b c t : F) (r : ℕ) :
    chordCoefficient x xx (fun i => q i-t*s i) a b c r =
      a*(chordCoefficient x xx q 1 0 0 r-t*chordCoefficient x xx s 1 0 0 r) +
      b*(chordCoefficient x xx q 0 1 0 r-t*chordCoefficient x xx s 0 1 0 r) +
      c*(chordCoefficient x xx q 0 0 1 r-t*chordCoefficient x xx s 0 0 1 r) := by
  have h := chordCoefficient_linear x xx q s a b c 1 (-t) r
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at h
  rw [h, chordCoefficient_components x xx q, chordCoefficient_components x xx s]
  ring

#print axioms active_source_six_constants
#print axioms chordCoefficient_linear
#print axioms chordCoefficient_components
#print axioms chordEven_linear
#print axioms chordOdd_linear
#print axioms chordEven_components
#print axioms chordOdd_components
#print axioms scatter_run_value
#print axioms scatter_value_linear
end AspisV8R17
