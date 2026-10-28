import NDO_JFw_TX2_CircleFormula
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Query0
open Aeneas Aeneas.Std Result

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    JFv_TX2_Query0Obligation.Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_Query0Formula.source err seed
  rw [JFw_TX2_Dots0.source,JFw_TX2_CircleFormula.formula] at sem
  have selected : JFw_TX2_CircleNumbers.value=
      CheckpointBytes5Output.ofE JFv_TX2_Query0Obligation.selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE JFv_TX2_Query0Obligation.selected) := by
    change ((2028222263<2147483647 ∧ 814288248<2147483647) ∧
      (354118641<2147483647 ∧ 1376248873<2147483647)) ∧
      ((1642244954<2147483647 ∧ 2101120408<2147483647) ∧
      (22065465<2147483647 ∧ 1602413776<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := by
    have h := (SAQ_WideABI.w_canonical out).mp canon
    exact h
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out)
    (FIo_Install.toE JFv_TX2_Query0Obligation.selected) co csel (sem.trans selected)
  have same : out=JFv_TX2_Query0Obligation.selected := congrArg FIo_Install.fromE sameNative
  unfold JFv_TX2_Query0Obligation.Goal
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JFw_TX2_Query0
end
