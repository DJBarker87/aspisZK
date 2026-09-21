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

def zeroExtend (n : ℕ) (q : ℕ → F) (i : ℕ) : F := if i<n then q i else 0

theorem zeroExtend_linear (n : ℕ) (q s : ℕ → F) (a b : F) :
    zeroExtend n (fun i => a*q i+b*s i) =
      fun i => a*zeroExtend n q i+b*zeroExtend n s i := by
  funext i
  unfold zeroExtend
  split <;> simp

theorem scatter_zeroExtend_input (edges : List (ScatterEdge ℕ ℕ F))
    (n : ℕ) (h : ∀ e ∈ edges, e.1<n) (q : ℕ → F) (r : ℕ) :
    scatterValue edges (zeroExtend n q) r = scatterValue edges q r := by
  unfold scatterValue
  congr 1
  apply List.map_congr_left
  intro e he
  simp only [zeroExtend, if_pos (h e he)]

theorem scatter_zero_above (edges : List (ScatterEdge ℕ ℕ F))
    (n : ℕ) (h : ∀ e ∈ edges, e.2.1<n) (q : ℕ → F)
    (r : ℕ) (hr : n≤r) : scatterValue edges q r = 0 := by
  induction edges with
  | nil => simp [scatterValue]
  | cons e es ih =>
      have he : r ≠ e.2.1 := by
        intro eq
        have := h e (by simp)
        omega
      have hs : ∀ e ∈ es, e.2.1<n := fun e he => h e (by simp [he])
      simp only [scatterValue, List.map_cons, List.sum_cons, if_neg he, zero_add]
      exact ih hs

theorem scatter_zeroExtend_output (edges : List (ScatterEdge ℕ ℕ F))
    (n : ℕ) (h : ∀ e ∈ edges, e.2.1<n) (q : ℕ → F) :
    zeroExtend n (scatterValue edges q) = scatterValue edges q := by
  funext r
  unfold zeroExtend
  split
  · rfl
  · exact (scatter_zero_above edges n h q r (by omega)).symm

theorem zeroExtend_parity (n : ℕ) (q : ℕ → F) (r b : ℕ) (hb : b<2) :
    zeroExtend n (fun i => q (2*i+b)) r = zeroExtend (2*n) q (2*r+b) := by
  have h : r<n ↔ 2*r+b<2*n := by omega
  simp only [zeroExtend, h]

/-- Dropping a high tail does not change any retained coefficient. It does
not establish the source's separate high-tail-zero acceptance assertion. -/
theorem zeroExtend_retained (n : ℕ) (q : ℕ → F) (r : ℕ) (hr : r<n) :
    zeroExtend n q r = q r := by simp [zeroExtend, hr]

def finiteChordEven (n : ℕ) (x xx : List (ScatterEdge ℕ ℕ F))
    (q : ℕ → F) (a b c : F) (r : ℕ) : F :=
  let e := zeroExtend n (fun i => q (2*i))
  let o := zeroExtend n (fun i => q (2*i+1))
  let xe := zeroExtend (n+1) (scatterValue x e)
  let xo := zeroExtend (n+1) (scatterValue x o)
  let xxo := zeroExtend (n+2) (scatterValue xx xo)
  a*e r+b*xe r+c*(o r-xxo r)

def finiteChordOdd (n : ℕ) (x : List (ScatterEdge ℕ ℕ F))
    (q : ℕ → F) (a b c : F) (r : ℕ) : F :=
  let e := zeroExtend n (fun i => q (2*i))
  let o := zeroExtend n (fun i => q (2*i+1))
  let xo := zeroExtend (n+1) (scatterValue x o)
  c*e r+a*o r+b*xo r

theorem finiteChordEven_eq (n : ℕ) (x xx : List (ScatterEdge ℕ ℕ F))
    (hx : ∀ e ∈ x, e.2.1<n+1) (hxx : ∀ e ∈ xx, e.2.1<n+2)
    (q : ℕ → F) (a b c : F) (r : ℕ) :
    finiteChordEven n x xx q a b c r = chordEven x xx (zeroExtend (2*n) q) a b c r := by
  have he : zeroExtend n (fun i => q (2*i)) = fun i => zeroExtend (2*n) q (2*i) := by
    funext i
    simpa using zeroExtend_parity n q i 0 (by decide)
  have ho : zeroExtend n (fun i => q (2*i+1)) = fun i => zeroExtend (2*n) q (2*i+1) := by
    funext i
    exact zeroExtend_parity n q i 1 (by decide)
  simp only [finiteChordEven, scatter_zeroExtend_output x (n+1) hx,
    scatter_zeroExtend_output xx (n+2) hxx]
  rw [he,ho]
  rfl

theorem finiteChordOdd_eq (n : ℕ) (x : List (ScatterEdge ℕ ℕ F))
    (hx : ∀ e ∈ x, e.2.1<n+1)
    (q : ℕ → F) (a b c : F) (r : ℕ) :
    finiteChordOdd n x q a b c r = chordOdd x (zeroExtend (2*n) q) a b c r := by
  have he : zeroExtend n (fun i => q (2*i)) = fun i => zeroExtend (2*n) q (2*i) := by
    funext i
    simpa using zeroExtend_parity n q i 0 (by decide)
  have ho : zeroExtend n (fun i => q (2*i+1)) = fun i => zeroExtend (2*n) q (2*i+1) := by
    funext i
    exact zeroExtend_parity n q i 1 (by decide)
  simp only [finiteChordOdd, scatter_zeroExtend_output x (n+1) hx]
  rw [he,ho]
  rfl

def finiteChordCoefficient (n : ℕ) (x xx : List (ScatterEdge ℕ ℕ F))
    (q : ℕ → F) (a b c : F) (r : ℕ) : F :=
  if r%2=0 then finiteChordEven n x xx q a b c (r/2)
  else finiteChordOdd n x q a b c (r/2)

theorem finiteChordCoefficient_eq (n : ℕ) (x xx : List (ScatterEdge ℕ ℕ F))
    (hx : ∀ e ∈ x, e.2.1<n+1) (hxx : ∀ e ∈ xx, e.2.1<n+2)
    (q : ℕ → F) (a b c : F) (r : ℕ) :
    finiteChordCoefficient n x xx q a b c r =
      chordCoefficient x xx (zeroExtend (2*n) q) a b c r := by
  simp only [finiteChordCoefficient, chordCoefficient,
    finiteChordEven_eq n x xx hx hxx, finiteChordOdd_eq n x hx]

theorem finite_source_six_constants (n : ℕ) (x xx : List (ScatterEdge ℕ ℕ F))
    (hx : ∀ e ∈ x, e.2.1<n+1) (hxx : ∀ e ∈ xx, e.2.1<n+2)
    (q s : ℕ → F) (a b c t : F) (r : ℕ) :
    finiteChordCoefficient n x xx (fun i => q i-t*s i) a b c r =
      a*(finiteChordCoefficient n x xx q 1 0 0 r-t*finiteChordCoefficient n x xx s 1 0 0 r) +
      b*(finiteChordCoefficient n x xx q 0 1 0 r-t*finiteChordCoefficient n x xx s 0 1 0 r) +
      c*(finiteChordCoefficient n x xx q 0 0 1 r-t*finiteChordCoefficient n x xx s 0 0 1 r) := by
  have hz := zeroExtend_linear (2*n) q s 1 (-t)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hz
  simp only [finiteChordCoefficient_eq n x xx hx hxx]
  rw [hz]
  exact active_source_six_constants x xx (zeroExtend (2*n) q) (zeroExtend (2*n) s) a b c t r

#print axioms finiteChordCoefficient_eq
#print axioms finite_source_six_constants
#print axioms finiteChordEven_eq
#print axioms finiteChordOdd_eq
#print axioms zeroExtend_parity
#print axioms zeroExtend_retained
#print axioms zeroExtend_linear
#print axioms scatter_zeroExtend_input
#print axioms scatter_zero_above
#print axioms scatter_zeroExtend_output
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
