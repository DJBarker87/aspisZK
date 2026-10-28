import NDO_JFz_TX2_Q1_CircleFormula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value11_2.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 1).x)⁻¹=(840707391 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 90208729 840707391 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 1).y)⁻¹=(1785601017 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 670446566 1785601017 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 1) 2#usize=ok selected := JFn_Values11.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 1)
    (JFv_TX2_CircleGeometry.inverse err seed 1)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 1
  rw [x,y,JFz_TX2_Q1_Dots0.source,JFz_TX2_Q1_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q1_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((12674944<2147483647 ∧ 1246410058<2147483647) ∧ (116774269<2147483647 ∧ 918536601<2147483647)) ∧
      ((1000197073<2147483647 ∧ 68609528<2147483647) ∧ (19935596<2147483647 ∧ 1874953030<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q1_Query
end
