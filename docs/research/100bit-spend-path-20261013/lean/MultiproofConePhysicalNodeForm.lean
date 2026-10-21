import MultiproofConePhysicalPrelude

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalNodeForm
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalNode MultiproofConePhysicalPrelude
open MultiproofConeNodeDomain MultiproofConeLiveReference
open AspisV8R19.MemoizedProgramLaw

/-- The physical node really is zero or one oracle request, with exactly the
observed child reads and the source checked writer as its continuation. This
is Program equality, not inferred from equal returned Results. -/
theorem node_form (s : reference.Scratch) (physical : Slice U8) (i w : Usize)
    (domain : RowDomain physical s i w) (active : i.val<s.n.val) :
    node s physical i w = .done (.ok (.Stop s)) ∨
    ∃ left right ni cursor, Input physical s i left right ni cursor ∧
      node s physical i w=writer s left right ni cursor s.idx.val[i.val]! w := by
  have ib : i.val<16 := by have := domain.2.1;omega
  have idx := array_read s.idx i ib
  have val := array_read s.val i ib
  obtain ⟨ni,add,niVal⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
  have nv : ni.val=i.val+1 := by scalar_tac
  unfold node
  rw [idx,checked,val,checked,add,checked]
  by_cases more : ni<s.n
  · rw [if_pos more]
    have nib : ni.val<16 := by have := domain.2.1;scalar_tac
    rw [array_read s.idx ni nib,checked]
    by_cases pair : s.idx.val[ni.val]! = s.idx.val[i.val]! ^^^ 1#u32
    · rw [if_pos pair,array_read s.val ni nib,checked]
      obtain ⟨next,add2,nextVal⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x:=i) (y:=2#usize) (by scalar_tac))
      rw [add2,checked]
      apply Or.inr
      refine ⟨s.val.val[i.val]!,s.val.val[ni.val]!,next,s.«at»,?_,rfl⟩
      have sp : SourcePair s i := by
        refine ⟨by scalar_tac,?_⟩
        simpa only [nv] using pair
      simp only [Input,sp,if_true,nv]
      exact ⟨trivial,trivial,by scalar_tac,trivial⟩
    · rw [if_neg pair]
      have np : ¬SourcePair s i := by
        intro sp
        exact pair (by simpa only [nv] using sp.2)
      rcases supply_form s physical i ni w domain np nv with stopped | running
      · exact Or.inl stopped
      · obtain ⟨left,right,cursor,input,eq⟩ := running
        exact Or.inr ⟨left,right,ni,cursor,input,eq⟩
  · rw [if_neg more]
    have np : ¬SourcePair s i := by intro sp;have lt := sp.1;apply more;change ni.val<s.n.val;omega
    rcases supply_form s physical i ni w domain np nv with stopped | running
    · exact Or.inl stopped
    · obtain ⟨left,right,cursor,input,eq⟩ := running
      exact Or.inr ⟨left,right,ni,cursor,input,eq⟩

#print axioms node_form
end AspisR1.MultiproofConePhysicalNodeForm
