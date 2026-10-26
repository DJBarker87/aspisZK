import FIw_PublicModel
import R0P.Path
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_Marginals
open FIv_NativeValue (K)
open FIw_PublicModel (Selectors)

theorem high (s : Selectors)
    (mass : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val) = 1) (h : Fin 64) :
    R0P.g2High (FIw_PublicModel.selector s) h = FIv_NativeArray.value s.high h.val := by
  unfold R0P.g2High FIw_PublicModel.selector R0P.g2Row
  have address (l : Fin 16) : (16*h.val+l.val)/16=h.val ∧ (16*h.val+l.val)%16=l.val := by omega
  simp_rw [(address _).1,(address _).2]
  rw [←Finset.mul_sum,mass,mul_one]

theorem low (s : Selectors)
    (mass : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val) = 1) (l : Fin 16) :
    R0P.g2Low (FIw_PublicModel.selector s) l = FIv_NativeArray.value s.low l.val := by
  unfold R0P.g2Low FIw_PublicModel.selector R0P.g2Row
  have address (h : Fin 64) : (16*h.val+l.val)/16=h.val ∧ (16*h.val+l.val)%16=l.val := by omega
  simp_rw [(address _).1,(address _).2]
  rw [←Finset.sum_mul,mass,one_mul]
#print axioms high
#print axioms low
end AspisR1.FIz_Marginals
end
