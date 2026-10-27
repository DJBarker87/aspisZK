import RPu_FJj_QMSliceUpdate
import RPt_FJc_WeightConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_QMOne
open AspisR1CurrentWide.Proof

theorem source : FIo_Install.toQ FIn_WeightsExtract.field.QM31.ONE=
    FIo_Native.aspis_core.field.QM31.ONE := by
  simp only [FIo_Install.toQ,FIn_WeightsExtract.field.QM31.ONE,FIo_Native.aspis_core.field.QM31.ONE]

theorem canon : FIo_QMValues.Canon FIo_Native.aspis_core.field.QM31.ONE := by
  have h := FJc_WeightConstants.one.1
  change FIo_QMValues.Canon (FIo_Install.toQ FIn_WeightsExtract.field.QM31.ONE) at h
  rw [source] at h
  exact h

theorem value : decodeQM (FIo_FieldBridge.qm FIo_Native.aspis_core.field.QM31.ONE)=1 := by
  have h := FJc_WeightConstants.one.2
  change decodeQM (FIo_FieldBridge.qm (FIo_Install.toQ FIn_WeightsExtract.field.QM31.ONE))=1 at h
  rw [source] at h
  exact h
#print axioms source
#print axioms canon
#print axioms value
end AspisR1.FJj_QMOne
end
