set_option autoImplicit false
namespace NND_BoolReject

theorem or_guard {A : Type} (b c : Bool) (err rest : A) :
 (if b || c then err else rest) = if b then err else if c then err else rest := by
 cases b <;> cases c <;> rfl

theorem not_guard {A : Type} (b : Bool) (err rest : A) :
 (if !b then err else rest) = if b then rest else err := by
 cases b <;> rfl

theorem eight {A : Type} (a b c d e f g h : Bool) (err good : A) :
 (if a then if b then if c then if d then if e then if f then
   if g then err else if h then good else err
   else err else err else err else err else err else err) =
 (if !a || (!b || !c || !d || !e || !f || g || !h) then err else good) := by
 cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
 cases g <;> cases h <;> rfl

theorem ten {A : Type} (a b c d e f g h i j : Bool) (err good : A) :
 (if a then if b then if c then if d then if e then
   if f then err else if g then if h then if i then if j then good else err
   else err else err else err else err else err else err else err else err) =
 (if !a || !b || !c || !d || !e || f || !g || !h || !i || !j then err else good) := by
 cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
 cases g <;> cases h <;> cases i <;> cases j <;> rfl

#print axioms ten
#print axioms eight
#print axioms or_guard
#print axioms not_guard
end NND_BoolReject
