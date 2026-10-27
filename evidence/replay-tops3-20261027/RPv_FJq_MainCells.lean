import RPv_FJn_MainArrayValue
import RPv_FJn_MainClaims
import RPv_FJn_MaskWide
import RPv_FJn_MainPoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MainCells
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (decode)
open FIz_ConcretePack (embed)
def cell {N : Usize} (a : Array MQ N) (i : Fin N.val) : MQ :=
  a.val[i.val]'(by rw [a.property];exact i.isLt)
theorem read {N : Usize} (a : Array MQ N) (i : Usize) (x : MQ)
    (run : Array.index_usize a i=ok x) : FJn_MainArrayValue.value a i.val=decode x :=
  FJn_MainArrayValue.read a i x run
theorem bounded {N : Usize} (a : Array MQ N) (i : Fin N.val) :
    FJn_MainArrayValue.value a i.val=decode (cell a i) := by
  unfold FJn_MainArrayValue.value cell
  rw [List.getElem?_eq_getElem (by rw [a.property];exact i.isLt)]
theorem point (a : Array MQ 10#usize) (i : Fin 10) :
    FJn_MaskWide.cell10 a i=embed (FJn_MainPoint.point a i) := rfl
#print axioms read
#print axioms bounded
#print axioms point
end AspisR1.FJq_MainCells
end
