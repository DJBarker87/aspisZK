import AspisR618SelectedMatrix.Funs
import AspisV8R19.R159WideBaseExecution
import AspisV8R19.R161WrappedMulExecution

set_option autoImplicit false

namespace AspisV8R19.R619MatrixArithmeticBridge
open Aeneas Aeneas.Std
open AspisV8R15.ExactTowerBase (M31Exact)
open AspisV8R19.ComplexBaseExecution (encodeBase)

theorem actual_add_eq_reference_all (x y : Aeneas.Std.U32) :
    AspisR618SelectedMatrix.aspis_core.field.M31.add x y =
      AspisR156FullFreeze.aspis_core.field.M31.add x y := by
  simp only [AspisR618SelectedMatrix.aspis_core.field.M31.add,
    AspisR156FullFreeze.aspis_core.field.M31.add,
    AspisR618SelectedMatrix.aspis_core.field.r91_raw_add,
    AspisR156FullFreeze.aspis_core.field.r91_raw_add,
    AspisR156FullFreeze.aspis_core.field.P]

theorem actual_add_eq_reference (a b : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.add (encodeBase a) (encodeBase b) =
      AspisR156FullFreeze.aspis_core.field.M31.add (encodeBase a) (encodeBase b) := by
  let s := U64.wrapping_add
    (core.convert.num.FromU64U32.from (encodeBase a))
    (core.convert.num.FromU64U32.from (encodeBase b))
  have hv : s.val = (encodeBase a).val + (encodeBase b).val := by
    dsimp only [s]
    rw [AspisV8R19.R159WideBaseExecution.add64_val]
    · simp only [core.convert.num.FromU64U32.from_val_eq]
    · simp only [core.convert.num.FromU64U32.from_val_eq,
        AspisV8R19.ComplexBaseExecution.encodeBase_val]
      have ha : a.val < AspisV8R15.ExactTowerBase.P := ZMod.val_lt a
      have hb : b.val < AspisV8R15.ExactTowerBase.P := ZMod.val_lt b
      simp [AspisV8R15.ExactTowerBase.P] at ha hb
      omega
  have hmax : ¬ s > core.convert.num.FromU64U32.from core.num.U32.MAX := by
    simp only [UScalar.lt_equiv, core.convert.num.FromU64U32.from_val_eq]
    change ¬ (4294967295 < s.val)
    rw [hv]
    have ha : (encodeBase a).val < 2147483647 := by
      rw [AspisV8R19.ComplexBaseExecution.encodeBase_val]
      exact ZMod.val_lt a
    have hb : (encodeBase b).val < 2147483647 := by
      rw [AspisV8R19.ComplexBaseExecution.encodeBase_val]
      exact ZMod.val_lt b
    omega
  simp only [AspisR618SelectedMatrix.aspis_core.field.M31.add,
    AspisR156FullFreeze.aspis_core.field.M31.add,
    lift, bind_tc_ok]
  have hmax_expr : ¬
      (core.convert.num.FromU64U32.from (encodeBase a)).wrapping_add
        (core.convert.num.FromU64U32.from (encodeBase b)) >
          core.convert.num.FromU64U32.from core.num.U32.MAX := by
    simpa only [s] using hmax
  simp only [hmax_expr, if_false, AspisR156FullFreeze.aspis_core.field.P]

end AspisV8R19.R619MatrixArithmeticBridge
