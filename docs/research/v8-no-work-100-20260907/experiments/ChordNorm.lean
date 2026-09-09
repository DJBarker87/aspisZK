import Mathlib.Tactic
namespace AspisV8.ChordNorm
variable {R : Type*} [CommRing R]
def norm (r a b : R) := a^2-r*b^2
def polar (r a b c d : R) := 2*(a*c-r*b*d)
def even (r a b c d e f x y : R) := norm r a b+norm r c d*x^2+norm r e f*y^2

theorem polarized (r a b c d e f x y : R) :
    norm r (a+c*x+e*y) (b+d*x+f*y) =
    even r a b c d e f x y+polar r a b c d*x+
      polar r a b e f*y+polar r c d e f*(x*y) := by
  dsimp [norm,polar,even]; ring

-- Source ordering (++,+-,--,-+); two butterfly pairs reuse the same
-- even/odd terms. Valid at arbitrary points, not only x^2+y^2=1.
theorem four_slots (r a b c d e f x y : R) :
    (norm r (a+c*x+e*y) (b+d*x+f*y),
     norm r (a+c*x-e*y) (b+d*x-f*y),
     norm r (a-c*x-e*y) (b-d*x-f*y),
     norm r (a-c*x+e*y) (b-d*x+f*y)) =
    (let t:=even r a b c d e f x y
     let u:=polar r a b c d*x
     let v:=polar r a b e f*y
     let w:=polar r c d e f*(x*y)
     ((t+u)+(v+w),(t+u)-(v+w),(t-u)-(v-w),(t-u)+(v-w))) := by
  dsimp [norm,polar,even]; ext <;> ring

-- The represented CM31 multiplication by tower constant r=2+i. This is
-- separate from treating the first norm's abstract coefficient ring as CM31.
theorem times_r_coordinates (a b : R) :
    (2*a-b,a+2*b) = (2*a+(-1)*b,1*a+2*b) := by ext <;> ring

-- A possible further circle-only specialization is deliberately NOT used by
-- the six-coefficient Rust control; dropping y^2 without this premise is false.
theorem circle_even (a b c x y : R) (h : x^2+y^2=1) :
    a+b*x^2+c*y^2 = (a+c)+(b-c)*x^2 := by
  linear_combination c*h

#print axioms polarized
#print axioms four_slots
#print axioms times_r_coordinates
#print axioms circle_even
end AspisV8.ChordNorm
