import Port3_NativeGeometryBody

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_GeometryStage
open Aeneas Aeneas.Std Result AspisR1Stage2
variable {CoreError : Type}

def geometry (ops : Port3_NativeGeometryBody.Ops CoreError) (queries : Array U32 22#usize)
    (start end1 : Usize) :=
  Port3_QueryInstall.result (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range ops queries start end1)

def installed (base : VTop_Stages.Ops) (ops : Port3_NativeGeometryBody.Ops CoreError) : VTop_Stages.Ops :=
  {base with op11 := geometry ops}

theorem queries_length (queries : Array U32 22#usize) :
    (Slice.len (Array.to_slice queries)).val=22 := by
  change queries.val.length=22
  exact queries.property

theorem invalid_start (ops : Port3_NativeGeometryBody.Ops CoreError) (queries : Array U32 22#usize)
    (start end1 : Usize) (bad : start.val>end1.val) :
    geometry ops queries start end1=ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Query) := by
  unfold geometry Port3_NativeGeometryBody.verifier.QueryGeometry.for_range
  have guard : start>end1 := by scalar_tac
  rw [if_pos guard]
  rfl

theorem invalid_end (ops : Port3_NativeGeometryBody.Ops CoreError) (queries : Array U32 22#usize)
    (start end1 : Usize) (bad : end1.val>22) :
    geometry ops queries start end1=ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Query) := by
  by_cases order : start>end1
  · exact invalid_start ops queries start end1 order
  · unfold geometry Port3_NativeGeometryBody.verifier.QueryGeometry.for_range
    rw [if_neg order]
    simp only [lift,bind_tc_ok]
    have invalid : end1>Slice.len (Array.to_slice queries) := by
      change end1.val>(Slice.len (Array.to_slice queries)).val
      rw [queries_length]
      exact bad
    rw [if_pos invalid]
    rfl

theorem accepted_range (ops : Port3_NativeGeometryBody.Ops CoreError) (queries : Array U32 22#usize)
    (start end1 : Usize) (out : verifier.QueryGeometry)
    (accepted : geometry ops queries start end1=ok (.Ok out)) :
    start.val≤end1.val ∧ end1.val≤22 := by
  constructor
  · by_contra bad
    have reject := invalid_start ops queries start end1 (by omega)
    rw [reject] at accepted
    cases accepted
  · by_contra bad
    have reject := invalid_end ops queries start end1 (by omega)
    rw [reject] at accepted
    cases accepted

#print axioms queries_length
#print axioms invalid_start
#print axioms invalid_end
#print axioms accepted_range
end AspisR1.Port3_GeometryStage
end
