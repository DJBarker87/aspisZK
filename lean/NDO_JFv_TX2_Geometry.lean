import NDO_JFv_TX2_GatherLoop
import Port4C_GeometryRange
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Geometry
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody

theorem selected : Port4C_GeometryRange.selected JFo_Prepared.value.queries 10#usize 22#usize=
    ok JFv_TX2_GatherShape.selected := by
  obtain ⟨out,run,contents,length⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      (⟨10#usize,22#usize⟩ : core.ops.range.Range Usize)
      (Array.to_slice JFo_Prepared.value.queries) (by decide)
      (by change 22≤JFo_Prepared.value.queries.val.length;exact le_of_eq JFo_Prepared.value.queries.property.symm))
  have same : out=JFv_TX2_GatherShape.selected := by
    apply Subtype.ext
    exact contents.trans (by rfl)
  exact run.trans (congrArg Result.ok same)

theorem source {C : Type} (err : C) (seed : Ops C) :
    ∃ out : verifier.QueryGeometry,
      verifier.QueryGeometry.for_range (JFv_TX2_GeometryOps.install err seed)
        JFo_Prepared.value.queries 10#usize 22#usize=ok (.Ok out) ∧
      JFv_TX2_GatherLoop.Meaning out := by
  obtain ⟨out,run,meaning⟩ := JFv_TX2_GatherLoop.source err seed
  refine ⟨out,?_,meaning⟩
  rw [Port4C_GeometryRange.native_range _ _ _ _ (by decide) (by decide),selected,bind_tc_ok]
  exact run

def value {C : Type} (err : C) (seed : Ops C) : verifier.QueryGeometry := Classical.choose (source err seed)

theorem native {C : Type} (err : C) (seed : Ops C) :
    verifier.QueryGeometry.for_range (JFv_TX2_GeometryOps.install err seed)
      JFo_Prepared.value.queries 10#usize 22#usize=ok (.Ok (value err seed)) :=
  (Classical.choose_spec (source err seed)).1

theorem stage {C : Type} (err : C) (seed : Ops C) :
    Port3_GeometryStage.geometry (JFv_TX2_GeometryOps.install err seed)
      JFo_Prepared.value.queries 10#usize 22#usize=ok (.Ok (value err seed)) :=
  (Port3_QueryInstall.success_iff _ _).mpr (native err seed)

theorem meaning {C : Type} (err : C) (seed : Ops C) :
    JFv_TX2_GatherLoop.Meaning (value err seed) :=
  (Classical.choose_spec (source err seed)).2

#print axioms meaning
#print axioms selected
#print axioms source
#print axioms native
#print axioms stage
end AspisR1.JFv_TX2_Geometry
end
