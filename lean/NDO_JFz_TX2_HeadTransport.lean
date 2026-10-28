import NDO_JFw_TX2_Coefficients
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_HeadTransport
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def product (i : Fin 12) (slot : Fin 4) (j : Fin 8) (n : Nat) : Nat :=
  (cell (JFv_TX2_FromLimbsMeaning.limbs
    (JFw_TX2_Coefficients.value ⟨(JFv_TX2_TermMeaning.term n).val,by
      have:=(JFv_TX2_TermMeaning.term n).isLt;omega⟩)) j).val *
    (JFv_TX2_UpdateMeaning.scalar i slot (JFv_TX2_TermMeaning.term n)).val

def sum (i : Fin 12) (slot : Fin 4) (j : Fin 8) : Nat → Nat
  | 0 => 0
  | n+1 => sum i slot j n+product i slot j n

theorem term (i : Fin 12) (slot : Fin 4) (j : Fin 8) (n : Nat) :
    JFv_TX2_TermMeaning.product i slot j n=product i slot j n := by
  unfold JFv_TX2_TermMeaning.product product
  rw [JFw_TX2_Coefficients.limbs]

theorem source (i : Fin 12) (slot : Fin 4) (j : Fin 8) (n : Nat) :
    JFv_TX2_InnerMeaning.sum i slot j 0 n=sum i slot j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [JFv_TX2_InnerMeaning.sum,ih,sum,Nat.zero_add,term]
#print axioms term
#print axioms source
end AspisR1.JFz_TX2_HeadTransport
end
