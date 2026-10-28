import NDO_JFv_TX2_LineCall
import NDO_JFs_TX2_Geo11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Line11
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : U32 := 770791513#u32
theorem source0 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 218094#usize=ok value0 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo11.source0
  change z.val=((90208729*90208729%2147483647+90208729*90208729%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value0 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source0
def value1 : U32 := 397483683#u32
theorem source1 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 218092#usize=ok value1 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo11.source1
  change z.val=((586767722*586767722%2147483647+586767722*586767722%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value1 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source1
def value2 : U32 := 1376692134#u32
theorem source2 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 218095#usize=ok value2 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo11.source2
  change z.val=((670446566*670446566%2147483647+670446566*670446566%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value2 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source2
end AspisR1.JFv_TX2_Line11
end
