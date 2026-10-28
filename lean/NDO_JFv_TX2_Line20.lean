import NDO_JFv_TX2_LineCall
import NDO_JFs_TX2_Geo20
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Line20
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : U32 := 1932862456#u32
theorem source0 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 185637#usize=ok value0 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo20.source0
  change z.val=((746032528*746032528%2147483647+746032528*746032528%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value0 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source0
def value1 : U32 := 214621191#u32
theorem source1 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 185636#usize=ok value1 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo20.source1
  change z.val=((229792333*229792333%2147483647+229792333*229792333%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value1 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source1
def value2 : U32 := 717710175#u32
theorem source2 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 185639#usize=ok value2 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo20.source2
  change z.val=((430022341*430022341%2147483647+430022341*430022341%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value2 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source2
end AspisR1.JFv_TX2_Line20
end
