import CurrentWideQMField
import WideTower
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
abbrev E := field.wide_exact.WideExact
def CanonicalWide (x : E) : Prop := CanonicalQM x.c0 ∧ CanonicalQM x.c1
def decodeWide (x : E) : AspisWideTower.WideExact := ⟨decodeQM x.c0,decodeQM x.c1⟩
private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem wide_add_success (x y z : E) (hx : CanonicalWide x) (hy : CanonicalWide y)
    (h : field.wide_exact.WideExact.add x y = .ok z) :
    CanonicalWide z ∧ decodeWide z = decodeWide x + decodeWide y := by
  unfold field.wide_exact.WideExact.add at h
  rcases bind_ok_inv h with ⟨q0,h0,h⟩
  rcases bind_ok_inv h with ⟨q1,h1,h⟩
  have he : ({c0:=q0,c1:=q1} : E)=z := Result.ok.inj h
  subst z
  have hc0 := qm_add_success x.c0 y.c0 q0 hx.1 hy.1 h0
  have hc1 := qm_add_success x.c1 y.c1 q1 hx.2 hy.2 h1
  refine ⟨⟨hc0.1,hc1.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact hc0.2
  · exact hc1.2

#print axioms wide_add_success
end AspisR1CurrentWide.Proof
