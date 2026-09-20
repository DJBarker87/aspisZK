import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Lagrange

/-! Four-slot inversion used by the proposed low-coefficient mask block.
This is deterministic algebra, not a transcript distribution theorem. -/
set_option autoImplicit false
namespace AspisV8R16
variable {F : Type*} [Field F]

def splitA (v0 v1 v2 v3 : F) := (v0+v1+v2+v3)/4
def splitB (y v0 v1 v2 v3 : F) := (v0-v1-v2+v3)/(4*y)
def splitC (x v0 v1 v2 v3 : F) := (v0+v1-v2-v3)/(4*x)
def splitD (x y v0 v1 v2 v3 : F) := (v0-v1+v2-v3)/(4*x*y)

theorem four_slot_inverse (x y v0 v1 v2 v3 : F)
    (h4 : (4 : F) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    let a := splitA v0 v1 v2 v3
    let b := splitB y v0 v1 v2 v3
    let c := splitC x v0 v1 v2 v3
    let d := splitD x y v0 v1 v2 v3
    a+b*y+c*x+d*x*y=v0 ∧
    a-b*y+c*x-d*x*y=v1 ∧
    a-b*y-c*x+d*x*y=v2 ∧
    a+b*y-c*x-d*x*y=v3 := by
  dsimp [splitA, splitB, splitC, splitD]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem bounded_interpolate {n : ℕ} (t values : Fin n → F)
    (hinj : Function.Injective t) :
    ∃ p : Polynomial F, p.degree < n ∧ ∀ i, p.eval (t i) = values i := by
  classical
  have hi : Set.InjOn t (Finset.univ : Finset (Fin n)) :=
    fun _ _ _ _ h => hinj h
  refine ⟨Lagrange.interpolate Finset.univ t values, ?_, ?_⟩
  · simpa using Lagrange.degree_interpolate_lt values hi
  · intro i
    exact Lagrange.eval_interpolate_at_node values hi (Finset.mem_univ i)

/-- Every four-slot target on n distinct fibre roots is realized by four
polynomials of degree less than n. No random-schedule premise is needed. -/
theorem fibre_interpolation {n : ℕ} (t x y v0 v1 v2 v3 : Fin n → F)
    (hinj : Function.Injective t) (h4 : (4 : F) ≠ 0)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) :
    ∃ a b c d : Polynomial F,
      a.degree < n ∧ b.degree < n ∧ c.degree < n ∧ d.degree < n ∧
      ∀ i,
        a.eval (t i)+b.eval (t i)*y i+c.eval (t i)*x i+d.eval (t i)*x i*y i=v0 i ∧
        a.eval (t i)-b.eval (t i)*y i+c.eval (t i)*x i-d.eval (t i)*x i*y i=v1 i ∧
        a.eval (t i)-b.eval (t i)*y i-c.eval (t i)*x i+d.eval (t i)*x i*y i=v2 i ∧
        a.eval (t i)+b.eval (t i)*y i-c.eval (t i)*x i-d.eval (t i)*x i*y i=v3 i := by
  obtain ⟨a, ha, ea⟩ := bounded_interpolate t
    (fun i => splitA (v0 i) (v1 i) (v2 i) (v3 i)) hinj
  obtain ⟨b, hb, eb⟩ := bounded_interpolate t
    (fun i => splitB (y i) (v0 i) (v1 i) (v2 i) (v3 i)) hinj
  obtain ⟨c, hc, ec⟩ := bounded_interpolate t
    (fun i => splitC (x i) (v0 i) (v1 i) (v2 i) (v3 i)) hinj
  obtain ⟨d, hd, ed⟩ := bounded_interpolate t
    (fun i => splitD (x i) (y i) (v0 i) (v1 i) (v2 i) (v3 i)) hinj
  refine ⟨a,b,c,d,ha,hb,hc,hd,?_⟩
  intro i
  rw [ea i, eb i, ec i, ed i]
  exact four_slot_inverse (x i) (y i) (v0 i) (v1 i) (v2 i) (v3 i) h4 (hx i) (hy i)

#print axioms fibre_interpolation
#print axioms four_slot_inverse
end AspisV8R16
