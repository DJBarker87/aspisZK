import NDO_JFv_TX2_LineCall
import NDO_JFs_TX2_Geo14
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Line14
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : U32 := 1094632580#u32
theorem source0 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 166165#usize=ok value0 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo14.source0
  change z.val=((1485660594*1485660594%2147483647+1485660594*1485660594%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value0 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source0
def value1 : U32 := 1052851067#u32
theorem source1 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 166164#usize=ok value1 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo14.source1
  change z.val=((1723213126*1723213126%2147483647+1723213126*1723213126%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value1 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source1
def value2 : U32 := 1698415954#u32
theorem source2 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 166167#usize=ok value2 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JFs_TX2_Geo14.source2
  change z.val=((506851799*506851799%2147483647+506851799*506851799%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value2 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source2
end AspisR1.JFv_TX2_Line14
end
