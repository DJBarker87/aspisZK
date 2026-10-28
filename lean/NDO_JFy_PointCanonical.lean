import NDO_JFu_TerminalPrefix
import NDO_JFu_MaskInputs
import RPv_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PointCanonical
open Aeneas Aeneas.Std Result FIq_Native

theorem source : FIw_ArrayValue.canonical JFu_TerminalPrefix.alpha := by
  intro x hx
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hx
  subst x
  have bound : i<10 := by simpa only [JFu_TerminalPrefix.alpha,FIq_Carriers.mapArray,List.length_map,JFm_PartialAlpha.a10,List.length_cons,List.length_nil] using hi
  have hc := JFu_MaskInputs.point_canonical i bound
  simp only [JFu_TerminalPrefix.alpha,FIq_Carriers.mapArray,List.getElem_map]
  simp only [ExtractedMaskLinearLoop.pointAtNat,FIp_SemanticArithmetic.mapArray,List.getElem_map,JFu_MaskInputs.point] at hc
  exact hc
#print axioms source
end AspisR1.JFy_PointCanonical
end
