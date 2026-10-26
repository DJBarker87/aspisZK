import JFs_TX2_Inner
set_option autoImplicit false
namespace AspisR1.JFs_TX2_Iterator
open Aeneas Aeneas.Std Result
abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def cursor (k : Fin 8) : Usize := Usize.ofNat (min (4*k.val) 26) (by have:=k.isLt;scalar_tac)
def value (k : Fin 8) : Iter := ⟨{start:=cursor k,«end»:=26#usize},4#usize⟩

theorem next (k : Fin 7) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (value ⟨k.val,by have:=k.isLt;omega⟩)=
      ok (some (cursor ⟨k.val,by have:=k.isLt;omega⟩),value ⟨k.val+1,by have:=k.isLt;omega⟩) := by
  fin_cases k <;> rfl

theorem done : core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) (value 7)=ok (none,value 7) := by rfl

theorem initial : core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      {start:=0#usize,«end»:=26#usize} 4#usize=ok (value 0) := by rfl

theorem start (k : Fin 7) : (cursor ⟨k.val,by have:=k.isLt;omega⟩).val=4*k.val := by
  unfold cursor
  have h:=k.isLt
  scalar_tac

#print axioms next
#print axioms done
#print axioms initial
#print axioms start
end AspisR1.JFs_TX2_Iterator
