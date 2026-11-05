import NGV_Monad
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticArithmetic
theorem add (x y z : Usize) (value : z.val=x.val+y.val) : x+y=ok z := by
 obtain ⟨out,run,outValue⟩:=WP.spec_imp_exists
   (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
 have same : out=z := UScalar.eq_of_val_eq (outValue.trans value.symm)
 simpa only [same] using run
theorem div (size : Usize) : ∃ half : Usize,size/2#usize=ok half ∧ half.val=size.val/2 := by
 obtain ⟨half,run,value⟩:=UScalar.div_spec size (y:=2#usize) (by scalar_tac)
 exact ⟨half,run,value⟩
theorem next (row : U8) (live : row.val<27) :
 ∃ after : U8,after.val=row.val+1 ∧
 core.iter.range.IteratorRange.next core.iter.range.StepU8
  ({start:=row,«end»:=27#u8} : core.ops.range.Range U8)=
  ok (some row,{start:=after,«end»:=27#u8}) := by
 obtain ⟨⟨value,iter⟩,run,some,advance,finish⟩:=WP.spec_imp_exists
  (core.iter.range.IteratorRange.next_UScalar_some_spec
    (ty:=.U8) (cloneInst:=core.clone.CloneU8) (partialOrdInst:=core.cmp.PartialOrdU8)
    (by intro x;rfl) (by intro x y;rfl) ({start:=row,«end»:=27#u8} : core.ops.range.Range U8) live)
 refine ⟨iter.start,by simpa using advance,?_⟩
 cases iter
 simpa only [some,finish] using run
#print axioms add
#print axioms div
#print axioms next
end NGV_SemanticArithmetic
