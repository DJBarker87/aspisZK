import NDO_JFv_TX2_LineCall
import NDO_JFs_TX2_Geo17
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Line17
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : U32 := 2006341782#u32
theorem source0 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 21248#usize=ok value0 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo17.source0
  change z.val=((859053651*859053651%2147483647+859053651*859053651%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value0 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source0
def value1 : U32 := 2006341782#u32
theorem source1 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 21248#usize=ok value1 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo17.source1
  change z.val=((859053651*859053651%2147483647+859053651*859053651%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value1 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source1
def value2 : U32 := 1738820246#u32
theorem source2 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 21251#usize=ok value2 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo17.source2
  change z.val=((1965433398*1965433398%2147483647+1965433398*1965433398%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value2 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source2
end AspisR1.JFv_TX2_Line17
end
