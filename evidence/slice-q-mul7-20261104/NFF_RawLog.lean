import NFE_NFC_RawValues
import NEG_ProductAbstraction
import NEG_DotDomain
set_option autoImplicit false
namespace AspisR1.NFF_RawLog
open AspisV8R17.RawReducer

abbrev Words := Fin 4 → Nat
abbrev Log := Fin 16 → Nat

def operands (x y : Words) (i : Fin 16) : Nat × Nat :=
  match i.val with
  | 0 => (x 2,y 2) | 1 => (x 3,y 3) | 2 => (x 2,y 3) | 3 => (x 3,y 2)
  | 4 => (x 0,y 0) | 5 => (x 1,y 1) | 6 => (x 0,y 1) | 7 => (x 1,y 0)
  | 8 => (x 0,y 2) | 9 => (x 2,y 0) | 10 => (x 1,y 3) | 11 => (x 3,y 1)
  | 12 => (x 0,y 3) | 13 => (x 1,y 2) | 14 => (x 2,y 1) | _ => (x 3,y 0)

def exactProducts (x y : Words) : Log := fun i => (operands x y i).1*(operands x y i).2

def evaluate (p : Log) : Nat × Nat × Nat × Nat :=
  let u := foldBits (p 0+P*P-p 1)
  let v := foldBits (p 2+p 3)
  (p 4+P*P-p 5+2*u+3*P-v,
   p 6+p 7+u+2*v,
   p 8+p 9+2*P*P-p 10-p 11,
   p 12+p 13+p 14+p 15)

/-- Literal operand order agrees with the adopted raw coefficient formulas. -/
theorem natural (x y : Words) : evaluate (exactProducts x y)=
    R22RawQmProductResidues.rawCoefficients (x 0) (x 1) (x 2) (x 3)
      (y 0) (y 1) (y 2) (y 3) := by rfl

/-- Every local product reply is tied to its reached operands. No whole raw
reply is freely selected, and no field product is sent to Kani. -/
theorem same_log (x y : Words) (p : Log)
    (domain : ∀ i, (operands x y i).1<NEG_DotDomain.P ∧
      (operands x y i).2<NEG_DotDomain.P)
    (law : ∀ i,NEG_ProductAbstraction.Product 64
      (operands x y i).1 (operands x y i).2 (p i)) :
    p=exactProducts x y := by
  funext i
  have bound:=NEG_DotDomain.instantiate _ _ (domain i).1 (domain i).2
  have small : (operands x y i).1*(operands x y i).2<2^64 := by
    have cap : NEG_DotDomain.B<2^64 := by decide
    omega
  have h:=law i
  unfold NEG_ProductAbstraction.Product at h
  simpa only [Nat.mod_eq_of_lt small,exactProducts] using h

theorem replay (x y : Words) (p : Log)
    (domain : ∀ i, (operands x y i).1<NEG_DotDomain.P ∧
      (operands x y i).2<NEG_DotDomain.P)
    (law : ∀ i,NEG_ProductAbstraction.Product 64
      (operands x y i).1 (operands x y i).2 (p i)) :
    evaluate p=R22RawQmProductResidues.rawCoefficients
      (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2) (y 3) := by
  rw [same_log x y p domain law]
  exact natural x y

#print axioms natural
#print axioms same_log
#print axioms replay
end AspisR1.NFF_RawLog
