import NHI_TensorExactInner
import NHI_TensorOuterStep
set_option autoImplicit false
noncomputable section
namespace NHI_TensorExactOuter
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHI_TensorExactCell
abbrev W := FIo_Native.weights.Weights
abbrev Iter := core.ops.range.Range Usize

def expand (w : W) (k d : Usize) (hk : k.val<5) (hd : d.val<5)
 (n : Usize) (input : Slice NQ) : Slice NQ :=
 NHI_TensorExactInner.descend (rowAt w k d hk hd) n.val n.val input

theorem inner (w : W) (k d n : Usize) (hk : k.val<5) (hd : d.val<5)
 (hn : NHI_TensorDomains.Stage n.val)
 (hf : NHI_CellCanon.array (rowAt w k d hk hd)) (input : Slice NQ)
 (len : input.val.length=64) (ca : NHI_CellCanon.slice input) :
 FIo_Native.weights.Weights.tensor_loop0_loop0 (NHI_Reverse.cursor n) w k input n d=
 ok (w,expand w k d hk hd n input) ∧
 NHI_CellCanon.slice (expand w k d hk hd n input) ∧
 (expand w k d hk hd n input).val.length=64 := by
 obtain ⟨out,run,co,lo⟩ := NHI_TensorInnerTotal.source w k d n hk hd hn hf n (by omega) input len ca
 have precise := NHI_TensorExactInner.source w k d n hk hd hn hf n (by omega) input len ca
 have same := congrArg Prod.snd (Result.ok.inj (run.symm.trans precise))
 change out=expand w k d hk hd n input at same
 rw [same] at co lo
 exact ⟨precise,co,lo⟩

theorem active (w : W) (k d next n : Usize) (hk : k.val<5) (hd : d.val<5)
 (advance : next.val=d.val+1) (hn : NHI_TensorDomains.Stage n.val)
 (hf : NHI_CellCanon.array (rowAt w k d hk hd)) (input : Slice NQ)
 (len : input.val.length=64) (ca : NHI_CellCanon.slice input) :
 FIo_Native.weights.Weights.tensor_loop0.body k {start:=d,«end»:=5#usize} w input n=
 ok (cont ({start:=next,«end»:=5#usize},w,expand w k d hk hd n input,Usize.wrapping_mul n 4#usize)) ∧
 NHI_CellCanon.slice (expand w k d hk hd n input) ∧
 (expand w k d hk hd n input).val.length=64 := by
 have step := NHI_ForwardRange.exact_step {start:=d,«end»:=5#usize} next hd advance
 obtain ⟨run,co,lo⟩ := inner w k d n hk hd hn hf input len ca
 have rev : core.iter.traits.iterator.Iterator.rev.trait_default
  (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
  {start:=0#usize,«end»:=n}=ok (NHI_Reverse.cursor n) := rfl
 refine ⟨?_,co,lo⟩
 unfold FIo_Native.weights.Weights.tensor_loop0.body
 unfold NHI_ForwardRange.next at step
 rw [step]
 simp only [bind_tc_ok]
 dsimp! only
 rw [rev,bind_tc_ok,run]
 rfl

#print axioms inner
#print axioms active
end NHI_TensorExactOuter
end
