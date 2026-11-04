import NGD_AtReference
import NGD_RowPayload
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace NGD_AtDomains
/-- The real fixed-row schedule establishes both unchecked native additions
before each private forwarding call, independently of input acceptance. -/
theorem from_cursor (row : U8) (offset : Usize) (valid : row.val<27)
    (cursor : offset.val = NGD_SemanticSchedule.dst row.val) :
    ∃ tag size length finish,
      NGD_AtG.shape row = ok (some (tag,size)) ∧
      5#usize + size = ok length ∧ offset + length = ok finish ∧
      finish.val = NGD_SemanticSchedule.dst (row.val+1) ∧ finish.val ≤ 13831 := by
  obtain ⟨tag,size,shape⟩ := NGD_RowPayload.present row valid
  have sizeval := NGD_RowPayload.exact_size row tag size valid shape
  have bounds := NGD_SemanticSchedule.windows row.val valid
  have range : offset.val+5+size.val ≤ 13831 := by
    rw [cursor,sizeval]
    exact bounds.2.1
  have lenSpec : (5#usize+size : Result Usize) ⦃ r => r.val=5+size.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨length,lengthAdd,lengthVal⟩ := WP.spec_imp_exists lenSpec
  have endSpec : (offset+length : Result Usize) ⦃ r => r.val=offset.val+length.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨finish,endAdd,endVal⟩ := WP.spec_imp_exists endSpec
  have step := (NGD_SemanticSchedule.advance row.val valid).2
  refine ⟨tag,size,length,finish,shape,lengthAdd,endAdd,?_,?_⟩
  · rw [endVal,lengthVal,cursor,sizeval]
    omega
  · omega
#print axioms from_cursor
end NGD_AtDomains
