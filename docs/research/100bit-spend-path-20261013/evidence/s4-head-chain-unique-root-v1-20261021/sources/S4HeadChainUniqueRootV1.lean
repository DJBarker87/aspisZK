import S4HeadTailSharedWitnessRootV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsHeadChainUniqueRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1

/-- Actual source equations for the complete head dependency chain. All
operation results belong to the same inputs and operation record. -/
def HeadCore (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (iter : StepBy)
    (limbs : Array Std.U64 8#usize) (vals : Array Std.U32 8#usize) (body : Wide) : Prop :=
  core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
  BaseLoop ops iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs ∧
  ops.arrayFromFn 8#usize
    (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
    limbs = .ok vals ∧
  ops.wideFromLimbs vals = .ok (some body)

/-- Align independently exposed head and tail theorems without assuming
that their existential intermediate values happen to match. -/
theorem head_core_unique (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize)
    (iter1 iter2 : StepBy)
    (limbs1 limbs2 : Array Std.U64 8#usize)
    (vals1 vals2 : Array Std.U32 8#usize) (body1 body2 : Wide)
    (h1 : HeadCore ops a g slot iter1 limbs1 vals1 body1)
    (h2 : HeadCore ops a g slot iter2 limbs2 vals2 body2) :
    iter1 = iter2 ∧ limbs1 = limbs2 ∧ vals1 = vals2 ∧ body1 = body2 := by
  rcases h1 with ⟨hstep1,hbase1,harray1,hpack1⟩
  rcases h2 with ⟨hstep2,hbase2,harray2,hpack2⟩
  have hiter : iter1 = iter2 := Result.ok.inj (hstep1.symm.trans hstep2)
  subst iter2
  have hlimbs : limbs1 = limbs2 := Result.ok.inj (hbase1.symm.trans hbase2)
  subst limbs2
  have hvals : vals1 = vals2 := Result.ok.inj (harray1.symm.trans harray2)
  subst vals2
  have hbody : body1 = body2 := Option.some.inj (Result.ok.inj (hpack1.symm.trans hpack2))
  exact ⟨rfl,rfl,rfl,hbody⟩

#print axioms head_core_unique
end AspisR1FastDotsHeadChainUniqueRootV1
