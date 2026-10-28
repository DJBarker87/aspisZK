import NDO_JFv_TX2_GeometryReads
import NDO_JFs_TX2_Dots
import NDO_JFr_TX2_CircleAfterDots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_CircleGeometry
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E

def inverse {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) : Array U32 5#usize :=
  Classical.choose (JFv_TX2_GeometryReads.source err seed i)

theorem read {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) :
    Port5Q1_GeometryBinding.forQuery (JFv_TX2_Geometry.value err seed) (JFv_TX2_GeometryReads.cursor i)=ok (inverse err seed i) :=
  (Classical.choose_spec (JFv_TX2_GeometryReads.source err seed i)).1

theorem decoded {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) (j : Fin 5) :
    S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane (inverse err seed i) j)=
      (S7JoinBasisMachine.decode ((JFv_TX2_Rows.value i).words[j.val]?.getD 0#u32))⁻¹ :=
  (Classical.choose_spec (JFv_TX2_GeometryReads.source err seed i)).2.2 j

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) :
    ∃ out : E, FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value i) (inverse err seed i)=ok out ∧
      Port4C_QueryArithmetic.CanonE out ∧
      CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.circleWithInverses
        (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
        (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value i).x)⁻¹)
        (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value i).y)⁻¹)
        (Port5Q1_OpeningValues.values (JFs_TX2_Dots.value i)) := by
  obtain ⟨out,run,canon⟩ := JFr_TX2_CircleArray.source JFq_Alpha0.scalar
    (JFs_TX2_Dots.value i) (inverse err seed i) JFr_TX2_CircleArray.alpha0
    (fun j => JFs_TX2_Dots.canonical i _ (List.getElem_mem (by rw [(JFs_TX2_Dots.value i).property];exact j.isLt)))
  have exactness := (FIp_CircleQuery.exact_circle _ _ _ _ run).1
  rw [decoded err seed i 0,decoded err seed i 1] at exactness
  exact ⟨out,run,canon,exactness⟩

#print axioms read
#print axioms decoded
#print axioms source
end AspisR1.JFv_TX2_CircleGeometry
end
