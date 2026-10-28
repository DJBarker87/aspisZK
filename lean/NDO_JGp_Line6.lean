import NDO_JFv_TX2_LineCall
import NDO_JGp_Geo6
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Line6
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
def value0 : U32 := 1251996309#u32
theorem source0 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 65593#usize=ok value0 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JGp_Geo6.source0
  change z.val=((156224156*156224156%2147483647+156224156*156224156%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value0 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source0
def value1 : U32 := 895487338#u32
theorem source1 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 65592#usize=ok value1 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JGp_Geo6.source1
  change z.val=((1120301530*1120301530%2147483647+1120301530*1120301530%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value1 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source1
def value2 : U32 := 1345719795#u32
theorem source2 : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations 65595#usize=ok value2 := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_LineCall.source _ _ JGp_Geo6.source2
  change z.val=((744539785*744539785%2147483647+744539785*744539785%2147483647)%2147483647+2147483647-1)%2147483647 at value
  norm_num at value
  have same : z=value2 := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms source2
end AspisR1.JGp_Line6
end
