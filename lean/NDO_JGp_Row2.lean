import NDO_JGp_Line2
import NDO_JFv_TX2_NodeCall
import JFv_TX2_GeometryOps
import Port4C_GeometryGather
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Row2
open Aeneas Aeneas.Std Result

def value : Port4C_GeometryGather.Row := ⟨2071054496#u32,1264348651#u32,203043952#u32,1661922674#u32,1699037283#u32⟩

theorem node : JFv_TX2_NodeCall.sourceCall value.lineX=ok value.lineZ := by
  obtain ⟨z,run,canon,hv⟩ := JFv_TX2_NodeCall.source value.lineX
  change z.val=((203043952*203043952%2147483647+203043952*203043952%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value.lineZ := UScalar.eq_of_val_eq hv
  exact same ▸ run

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    (JFv_TX2_GeometryOps.install err seed).op15 216823#usize=ok (⟨value.x,value.y⟩ : SAQ_Geometry.Point) ∧
    (JFv_TX2_GeometryOps.install err seed).op14 216820#usize=ok value.lineX ∧
    (JFv_TX2_GeometryOps.install err seed).op14 216823#usize=ok value.lineY ∧
    JFv_TX2_NodeCall.sourceCall value.lineX=ok value.lineZ := by
  refine ⟨?_,JGp_Line2.source1,JGp_Line2.source2,node⟩
  change (do let pt ← AspisR1QueryGeometryActual.fast_domain.fibre_point R17CurrentCM31Semantics.operations 216823#usize
             ok (⟨pt.x,pt.y⟩ : SAQ_Geometry.Point))=_
  rw [JGp_Geo2.source0,bind_tc_ok]
  rfl

theorem regular : ∀ a∈value.words,a.val<2147483647 ∧ a≠0#u32 := by
  intro a h
  simp only [value,Port4C_GeometryGather.Row.words,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms node
#print axioms source
#print axioms regular
end AspisR1.JGp_Row2
end
