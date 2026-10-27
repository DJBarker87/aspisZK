import FJr_InactiveRegroup
import FJr_InactiveRaw
import FJr_DualFold16
import FJr_QuarterSquared
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_InactiveMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE)
open scoped BigOperators
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (f : Slice U8) (low : Array NE 16#usize) (a0 a1 : FE)
    (vl : ∀ s,s<16 → FIp_ArrayValue.value low s=
      (decodeM FIo_Native.weights.QUARTER*decodeM FIo_Native.weights.QUARTER) •
        (a0^FJc_LowModel.perm (s%4)*a1^FJc_LowModel.perm (s/4))) :
    FJc_InactiveValue.sumPrefix f low 12=RoundPairing.dot
      (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) a1 (RoundPairing.dualFold (n:=256) a0 FJr_InactiveRaw.raw)) := by
  rw [FJr_InactiveRegroup.value,RoundPairing.dot]
  apply Finset.sum_congr rfl
  intro i _
  rw [FJr_DualFold16.value,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [vl u.val u.isLt,FJr_QuarterSquared.value,FJr_InactiveRaw.value]
  have recons : 4*(u.val/4)+u.val%4=u.val := by omega
  rw [recons]
  split <;> simp only [mul_one,mul_zero,zero_mul]
  ring

#print axioms value
end AspisR1.FJr_InactiveMeaning
end
