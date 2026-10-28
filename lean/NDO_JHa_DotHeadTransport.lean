import NDO_JFw_TX2_Coefficients
import NDO_JHa_DotHeadFlat
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotHeadTransport
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def product (d : JHa_DotContext.Data) (j : Fin 8) (n : Nat) : Nat :=
  (cell (JFv_TX2_FromLimbsMeaning.limbs
    (JFw_TX2_Coefficients.value ⟨(JHa_DotTermMeaning.term n).val,by
      have:=(JHa_DotTermMeaning.term n).isLt;omega⟩)) j).val *
    (d.scalars (JHa_DotTermMeaning.term n)).val

def sum (d : JHa_DotContext.Data) (j : Fin 8) : Nat → Nat
  | 0 => 0
  | n+1 => sum d j n+product d j n

theorem term (d : JHa_DotContext.Data) (j : Fin 8) (n : Nat) :
    JHa_DotTermMeaning.product d j n=product d j n := by
  unfold JHa_DotTermMeaning.product product
  rw [JFw_TX2_Coefficients.limbs]

theorem source (d : JHa_DotContext.Data) (j : Fin 8) (n : Nat) :
    JHa_DotInnerMeaning.sum d j 0 n=sum d j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [JHa_DotInnerMeaning.sum,ih,sum,Nat.zero_add,term]
#print axioms term
#print axioms source
end AspisR1.JHa_DotHeadTransport
end
