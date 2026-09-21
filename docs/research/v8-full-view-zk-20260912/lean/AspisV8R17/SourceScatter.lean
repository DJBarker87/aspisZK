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

#print axioms scatter_run_value
#print axioms scatter_value_linear
end AspisV8R17
