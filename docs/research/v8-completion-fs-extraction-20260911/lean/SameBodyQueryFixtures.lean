import SameBodyQueryClaim
namespace AspisV8Completion.SameBodyQueryFixtures
open SameBodyRelation SameBodyQueryClaim
def ops : SameBodyQueryClaim.Arithmetic Nat where
  zero := 0
  add := fun a b => (a+b)%17
  sub := fun a b => (a+17-b%17)%17
  mul := fun a b => (a*b)%17
  quarter := fun a => (13*a)%17
  evaluate7 := fun coefficients x =>
    (List.ofFn coefficients).reverse.foldl (fun a b => (a*x+b)%17) 0
def opened : Fin 22 → Nat := fun i => if i.val=0 then 1 else 0
#guard scales ops 2 4 == [2,4,8,16]
#guard increment ops 2 opened == 2
#guard injectClaim ops 10 2 opened == 12
#guard ops.sub 10 (increment ops 2 opened) == 8
#guard injectClaim ops 10 0 opened == 10
#guard injectClaim ops 10 2 (fun _ => 0) == 10
/-- A malformed sign bridge cannot identify the positive source increment
with the old consumer's subtracted callback value. Not a payment attack. -/
theorem source_sign_distinct :
    injectClaim ops 10 2 opened ≠ ops.sub 10 (increment ops 2 opened) := by decide
#print axioms source_sign_distinct
end AspisV8Completion.SameBodyQueryFixtures
