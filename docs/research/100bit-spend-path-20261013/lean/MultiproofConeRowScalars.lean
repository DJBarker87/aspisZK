import MultiproofConeLogicalPayload

set_option autoImplicit false
namespace AspisR1.MultiproofConeRowScalars
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeLogicalPayload

/-- Actual checked table lookup, division, addition and next-row operations,
including independent bounds for all reached row ordinals. -/
theorem scalars_total (row : U8) (bound : row.val<27) :
    ∃ tag size stored finish next,
      MultiproofParserRef.reference.row_shape row=ok (some (tag,size)) ∧
      (if row>=14#u8 then size/2#usize else ok size)=ok stored ∧
      5#usize+stored=ok finish ∧ row+1#u8=ok next ∧
      tag.val=(rowShape row.val).1 ∧ size.val=(rowShape row.val).2 ∧
      stored.val=storedSize row.val ∧ finish.val=5+stored.val ∧ next.val=row.val+1 := by
  obtain ⟨tag,size,table,tagValue,sizeValue⟩ := MultiproofConeRowShape.shape_total row bound
  have storage : ∃ stored : Usize,
      (if row>=14#u8 then size/2#usize else ok size)=ok stored ∧
      stored.val=storedSize row.val := by
    by_cases compact : row>=14#u8
    · obtain ⟨stored,hstored,hval⟩ := UScalar.div_spec (x:=size) (y:=2#usize) (by decide)
      refine ⟨stored,by simp only [compact,if_true,hstored],?_⟩
      have hc : 14≤row.val := compact
      simpa only [storedSize,hc,if_true,sizeValue,show (2#usize).val=2 from rfl] using hval
    · refine ⟨size,by simp only [compact,if_false],?_⟩
      have hc : ¬14≤row.val := compact
      simpa only [storedSize,hc,if_false] using sizeValue
  obtain ⟨stored,hstored,storedValue⟩ := storage
  have storedBound : stored.val≤3712 := by
    have h := (MultiproofConeRowShape.shape_properties row.val).2.1
    rw [storedValue,storedSize]
    split <;> omega
  obtain ⟨finish,hfinish,finishValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=5#usize) (y:=stored) (by scalar_tac))
  obtain ⟨next,hnext,nextValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=row) (y:=1#u8) (by scalar_tac))
  exact ⟨tag,size,stored,finish,next,table,hstored,hfinish,hnext,tagValue,sizeValue,
    storedValue,finishValue,nextValue⟩

#print axioms scalars_total
end AspisR1.MultiproofConeRowScalars
