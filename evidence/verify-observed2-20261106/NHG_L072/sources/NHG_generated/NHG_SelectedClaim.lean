import NHG_SnapshotViews
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHG_SelectedClaim
abbrev Q := FIq_Native.field.QM31
abbrev selected := FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim

theorem source (claims : Array Q 84#usize) (point column : Usize) :
 selected claims point column=(do
  let base←point*28#usize
  let index←base+column
  Array.index_usize claims index) := by
 unfold selected FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim
 rw [AspisR1.FIw_SelectedValue.width,bind_tc_ok]

theorem range (point column : Nat) (hp : point<3) (hc : column<28) :
 point*28+column<84 := by omega

/-- Exact same selected cell, all four raw words, with no field canonicality
hypothesis. Bounds come from this caller's point and column. -/
theorem returned (claims : Array Q 84#usize) (point column : Usize)
 (hp : point.val<3) (hc : column.val<28) :
 ∃ out,selected claims point column=ok out ∧
 out=claims.val[point.val*28+column.val]'(by simpa [claims.property] using range _ _ hp hc) := by
 have platform : 84≤Usize.max := by scalar_tac
 have mulCap : point.val*28≤Usize.max := by omega
 have mulSpec : (point*28#usize : Result Usize) ⦃b => b.val=point.val*28⦄ := by
  apply UScalar.mul_spec
  scalar_tac
 obtain ⟨base,baseCall,baseVal⟩:=WP.spec_imp_exists mulSpec
 have addCap : base.val+column.val≤Usize.max := by omega
 have addSpec : (base+column : Result Usize) ⦃i => i.val=base.val+column.val⦄ := by
  apply UScalar.add_spec
  simpa only [UScalar.max_USize_eq] using addCap
 obtain ⟨index,indexCall,indexVal⟩:=WP.spec_imp_exists addSpec
 have indexNat : index.val=point.val*28+column.val := by omega
 have inside : index.val<84 := by rw [indexNat];exact range _ _ hp hc
 obtain ⟨out,readCall,readValue⟩:=WP.spec_imp_exists
  (Array.index_usize_spec claims index (by simpa [Array.length,claims.property] using inside))
 refine ⟨out,?_,?_⟩
 · rw [source,baseCall,bind_tc_ok,indexCall,bind_tc_ok,readCall]
 · simpa only [indexNat] using readValue

#print axioms source
#print axioms range
#print axioms returned
end AspisR1.NHG_SelectedClaim
