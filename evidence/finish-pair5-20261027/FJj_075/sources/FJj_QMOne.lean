import FJj_QMSliceUpdate
import FJc_WeightConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_QMOne
open AspisR1CurrentWide.Proof

theorem canon : FIo_QMValues.Canon FIo_Native.aspis_core.field.QM31.ONE :=
  FJc_WeightConstants.one.1

theorem value : decodeQM (FIo_FieldBridge.qm FIo_Native.aspis_core.field.QM31.ONE)=1 :=
  FJc_WeightConstants.one.2
#print axioms canon
#print axioms value
end AspisR1.FJj_QMOne
end
