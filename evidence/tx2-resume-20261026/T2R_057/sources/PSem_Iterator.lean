import PSem_Control
import S1NativeCompactModelV1
set_option autoImplicit false
namespace AspisR1.PSem_Iterator
open Aeneas Aeneas.Std Result

def iter (start : U8) : core.ops.range.Range U8 :=
  {start:=start,«end»:=AspisS1NativeCompact.compact.SEMANTIC_ROWS}

theorem next_row (x y : U8) (bound : x.val<27) (successor : y.val=x.val+1) :
    core.iter.range.IteratorRange.next core.iter.range.StepU8 (iter x)=ok (some x,iter y) := by
  have within : x.val<U8.max := by scalar_tac
  simp [iter,AspisS1NativeCompact.compact.SEMANTIC_ROWS,core.iter.range.IteratorRange.next,
    core.iter.range.StepU8,core.iter.range.UScalarStep,
    core.cmp.PartialOrdU8,core.cmp.impls.PartialOrdU8.lt,
    core.clone.CloneU8,core.clone.impls.CloneU8.clone,
    liftFun1,liftFun2,core.iter.range.UScalarStep.forward_checked,bound,within]
  first
  | exact successor.symm
  | exact UScalar.eq_of_val_eq successor.symm
  | congr 2
    apply UScalar.eq_of_val_eq
    exact successor.symm

theorem successor_exists (x : U8) (bound : x.val<27) :
    ∃ y : U8, y.val=x.val+1 := by
  refine ⟨⟨x.val+1,?_⟩,rfl⟩
  scalar_tac

theorem finished (x : U8) (value : x.val=27) :
    core.iter.range.IteratorRange.next core.iter.range.StepU8 (iter x)=ok (none,iter x) := by
  simp [iter,AspisS1NativeCompact.compact.SEMANTIC_ROWS,core.iter.range.IteratorRange.next,
    core.iter.range.StepU8,core.iter.range.UScalarStep,
    core.cmp.PartialOrdU8,core.cmp.impls.PartialOrdU8.lt,liftFun2,value]

#print axioms next_row
#print axioms successor_exists
#print axioms finished
end AspisR1.PSem_Iterator
