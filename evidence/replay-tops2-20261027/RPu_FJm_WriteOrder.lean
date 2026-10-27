import RPu_FJc_ArrayUpdateValue
set_option autoImplicit false
namespace AspisR1.FJm_WriteOrder

theorem two {A : Type} (a b old : A) (j : Nat) :
    (if 1=j then b else if 0=j then a else old)=
      if j=0 then a else if j=1 then b else old := by
  by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> simp_all

theorem three {A : Type} (a b c old : A) (j : Nat) :
    (if 3=j then c else if 2=j then b else if 1=j then a else old)=
      if j=1 then a else if j=2 then b else if j=3 then c else old := by
  by_cases h1 : j=1 <;> by_cases h2 : j=2 <;> by_cases h3 : j=3 <;> simp_all
#print axioms two
#print axioms three
end AspisR1.FJm_WriteOrder
