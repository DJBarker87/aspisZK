import PV_B3_MaskFinite
import PV_B3_Mask117Finite
import PV_B3_PolynomialFinite
namespace PV_B3_BoundedPacket
open Aeneas Aeneas.Std Result
set_option autoImplicit false
 theorem forest134 :
    PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 = PV_B3_MaskFinite.reference :=
  PV_B3_MaskFinite.op134_bounded
 theorem mask117 (c1 : Array PV_B3_Copy_117.aspis_core.field.QM31 16#usize)
    (mask : Array PV_B3_Copy_117.aspis_core.field.QM31 10#usize)
    (g : PV_B3_Copy_117.aspis_core.field.QM31)
    (point : Array PV_B3_Copy_117.aspis_core.field.QM31 10#usize) :
    PV_B3_Copy_117.host_arithmetic.state_only_selected_mask_value c1 mask g point =
      PV_B3_Mask117Finite.reference c1 mask g point :=
  PV_B3_Mask117Finite.source_complete c1 mask g point
 theorem polynomial121 (poly : Array PV_B3_Copy_117.aspis_core.field.QM31 28#usize)
    (x : PV_B3_Copy_117.aspis_core.field.QM31) :
    PV_B3_Copy_117.host_arithmetic.evaluate_state_only_polynomial poly x =
      PV_B3_PolynomialFinite.reference poly x :=
  PV_B3_PolynomialFinite.source_complete poly x
-- These are bounded factorizations of emissions. No original/copy/row
-- equivalence, deployment closure or reached canonicality premise is asserted.
#print axioms forest134
#print axioms mask117
#print axioms polynomial121
end PV_B3_BoundedPacket
