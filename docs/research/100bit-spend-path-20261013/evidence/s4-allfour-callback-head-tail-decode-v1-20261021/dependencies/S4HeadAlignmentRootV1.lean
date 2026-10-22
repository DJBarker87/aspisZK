import S4HeadChainUniqueRootV1
import S4AllFourHeadDecodingV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsHeadAlignmentRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsConcreteTailInstallRootV1
open AspisR1FastDotsHeadChainUniqueRootV1
open AspisR1FastDotsAllFourHeadDecodingV1 (HeadOps Outer)
abbrev Ops := AspisR1FastDotsActualCallbackTailTraceRootV1.Ops

/-- Both existing source adapters produce the same operation record, so
head and tail source facts can be compared without an Ops equality premise. -/
theorem head_tail_ops_same (base : Ops) :
    HeadOps (install base) = install (Outer base) := by
  have hhead : HeadOps (install base) = Outer base := rfl
  have htail : install (Outer base) = Outer base := by
    cases base <;> rfl
  exact hhead.trans htail.symm

/-- Concrete specialization of deterministic source head alignment for the
actual operation records returned by the all-four head and tail theorems. -/
theorem source_heads_unique (base : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize)
    (iter1 iter2 : StepBy)
    (limbs1 limbs2 : Array Std.U64 8#usize)
    (vals1 vals2 : Array Std.U32 8#usize) (body1 body2 : Wide)
    (htail : HeadCore (install (Outer base)) a g slot iter1 limbs1 vals1 body1)
    (hhead : HeadCore (HeadOps (install base)) a g slot iter2 limbs2 vals2 body2) :
    iter1 = iter2 ∧ limbs1 = limbs2 ∧ vals1 = vals2 ∧ body1 = body2 := by
  rw [head_tail_ops_same] at hhead
  exact head_core_unique (install (Outer base)) a g slot iter1 iter2
    limbs1 limbs2 vals1 vals2 body1 body2 htail hhead

#print axioms head_tail_ops_same
#print axioms source_heads_unique
end AspisR1FastDotsHeadAlignmentRootV1
