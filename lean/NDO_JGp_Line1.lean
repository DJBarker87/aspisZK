import NDO_JFv_TX2_LineCall
import NDO_JGp_Geo1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Line1
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : U32 := 927254674#u32
theorem source0 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 147529#usize=ok value0 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JGp_Geo1.source0
  change z.val=((294074545*294074545%2147483647+294074545*294074545%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value0 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source0
def value1 : U32 := 1220228973#u32
theorem source1 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 147528#usize=ok value1 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JGp_Geo1.source1
  change z.val=((917223517*917223517%2147483647+917223517*917223517%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value1 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source1
def value2 : U32 := 1792229318#u32
theorem source2 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 147531#usize=ok value2 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JGp_Geo1.source2
  change z.val=((1076484827*1076484827%2147483647+1076484827*1076484827%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value2 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source2
end AspisR1.JGp_Line1
end
