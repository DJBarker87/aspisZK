import PV_B1_HostExternalFuns
import PV_B1_Carrier230
import PV_B1_CarrierWide
import PV_B1_Carrier258
import PV_B1_Transport
import PV_B1_SumOriginal
import PV_B1_PowersBridge
import PV_B1_PoleBridge
set_option autoImplicit false
noncomputable section
namespace PV_B1_Install
open Aeneas Aeneas.Std Result PV_B1_Host PV_B1_Transport
variable [ExternalTypes]
abbrev HQ := aspis_core.field.QM31
abbrev HW := aspis_core.field.wide_exact.WideExact
abbrev Rows := Slice (Array (Array HQ 2#usize) 2#usize)

def helper (h1 : Slice HQ) : Result (Option HQ) :=
  resultMap (Option.map PV_B1_Carrier230.fromQ)
    (PV_B1_230.state_only_copy_helper_sum (sliceMap PV_B1_Carrier230.toQ h1))

def powers (N : Usize) (x : HW) : Result (Array HW N) :=
  resultMap (arrayMap PV_B1_CarrierWide.fromW) (PV_B1_254.powers N (PV_B1_CarrierWide.toW x))

def rows (values : Rows) := sliceMap (arrayMap (arrayMap PV_B1_Carrier258.toQ)) values

def pole (values : Rows) (masks : Array U16 64#usize) (chi : HQ) : Result Bool :=
  PV_B1_258.all_slots_clear (rows values) masks (PV_B1_Carrier258.toQ chi)

def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op230 := helper, op254 := powers, op258 := pole}

theorem op230_source (ops : ExternalFuns) (h1 : Slice HQ) :
    (selected ops).op230 h1 =
      ok (Option.map PV_B1_Carrier230.fromQ
        (PV_B1_SumOriginal.original_row (sliceMap PV_B1_Carrier230.toQ h1))) := by
  change helper h1 = _
  unfold helper
  rw [PV_B1_SumOriginal.op230_source]
  rfl

theorem op254_source (ops : ExternalFuns) (N : Usize) (x : HW) :
    (selected ops).op254 N x =
      resultMap (arrayMap PV_B1_CarrierWide.fromW)
        (PV_B1_PowersOriginal.weights.powers N (PV_B1_CarrierWide.toW x)) := by
  change powers N x = _
  unfold powers
  rw [PV_B1_PowersBridge.op254_copy_equal_original]

theorem op258_source (ops : ExternalFuns) (values : Rows) (masks : Array U16 64#usize) (chi : HQ) :
    (selected ops).op258 values masks chi =
      PV_B1_PoleOriginal.reference.all_slots_clear (rows values) masks (PV_B1_Carrier258.toQ chi) := by
  change pole values masks chi = _
  unfold pole
  exact PV_B1_PoleBridge.op258_source _ _ _

-- No assertion that arbitrary foreign callbacks are the native implementation.
-- They are retained as the same pre-existing obligations.
theorem compressor_preserved (ops : ExternalFuns) : (selected ops).op223=ops.op223 := rfl

theorem wide_primitive_preserved (ops : ExternalFuns) : (selected ops).op47=ops.op47 := rfl
#print axioms op230_source
#print axioms op254_source
#print axioms op258_source
#print axioms compressor_preserved
#print axioms wide_primitive_preserved
end PV_B1_Install
