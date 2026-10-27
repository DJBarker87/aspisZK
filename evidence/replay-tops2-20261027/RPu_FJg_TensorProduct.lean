import RPu_FJg_TensorDigits
import R1RoundPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_TensorProduct
open scoped BigOperators
variable {E : Type} [Field E]

def high (f : Fin 5 → Fin 4 → E) (i : Fin 64) : E :=
  f 2 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩*
  f 3 ⟨i.val/4%4,Nat.mod_lt _ (by decide)⟩*
  f 4 ⟨i.val/16,by have := i.isLt;omega⟩

/-- Five symbolic tensor lanes; no source recurrence is evaluated. -/
theorem value (f : Fin 5 → Fin 4 → E) (i : Fin 64) (s t : Fin 4) :
    FJd_PointReference.tensor f (FJg_TensorDigits.index i s t)=f 0 t*f 1 s*high f i := by
  unfold FJd_PointReference.tensor
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,Fin.val_zero,Fin.val_succ,
    Nat.zero_add,pow_zero,pow_one,show 4^2=16 from by decide,show 4^3=64 from by decide,
    show 4^4=256 from by decide,Nat.div_one,mul_one,
    FJg_TensorDigits.zero,FJg_TensorDigits.one,FJg_TensorDigits.two,
    FJg_TensorDigits.three,FJg_TensorDigits.four]
  simp only [Fin.eta,
    show (0 : Fin 4).succ=(1 : Fin 5) from by decide,
    show (0 : Fin 3).succ.succ=(2 : Fin 5) from by decide,
    show (0 : Fin 2).succ.succ.succ=(3 : Fin 5) from by decide,
    show (0 : Fin 1).succ.succ.succ.succ=(4 : Fin 5) from by decide]
  unfold high
  ring

theorem children (i : Fin 64) (s t : Fin 4) :
    childIndex (childIndex i s) t=FJg_TensorDigits.index i s t := by
  apply Fin.ext
  dsimp only [childIndex,FJg_TensorDigits.index]
  omega
#print axioms value
#print axioms children
end AspisR1.FJg_TensorProduct
end
