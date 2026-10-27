import JGm_TX2_ReadCell
import JFq_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Supplied
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge

def prefix (nodes : Slice U8) (finish : Usize) : Slice U8 := MultiproofConeSlices.sub nodes 0#usize finish

theorem length (nodes : Slice U8) (finish : Usize) (bound : finish.val≤nodes.val.length) :
    (prefix nodes finish).val.length=finish.val := by
  simpa only [prefix,Nat.sub_zero] using MultiproofConeSlices.sub_length nodes 0#usize finish (by omega) bound
#print axioms length

theorem sub_prefix (nodes : Slice U8) (limit start finish : Usize)
    (order : start.val≤finish.val) (bound : finish.val≤limit.val) :
    MultiproofConeSlices.sub (prefix nodes limit) start finish=MultiproofConeSlices.sub nodes start finish := by
  apply Subtype.ext
  simp only [MultiproofConeSlices.sub,prefix,List.drop_zero,Nat.sub_zero]
  simpa only [Nat.zero_add] using JFq_Range.nested nodes.val 0 limit.val start.val (finish.val-start.val) (by omega)
#print axioms sub_prefix

theorem source (nodes : Slice U8) (cell : Nat) (limit start finish : Usize)
    (hs : start.val=32*cell) (hf : finish.val=32*cell+32)
    (bound : finish.val≤limit.val) (fits : limit.val≤nodes.val.length) :
    reference.read32 (MultiproofConeSlices.sub (prefix nodes limit) start finish)=
      ok (encodeState (JGh_TX2_NodeViews.readCell nodes cell)) := by
  rw [sub_prefix nodes limit start finish (by omega) bound]
  exact JGm_TX2_ReadCell.source nodes cell start finish hs hf (by omega)
#print axioms source

def nodes0 : Slice U8 := prefix JGh_TX2_NodeViews.nodes0 5216#usize
def nodes1 : Slice U8 := prefix JGh_TX2_NodeViews.nodes1 5216#usize
def nodes2 : Slice U8 := prefix JGh_TX2_NodeViews.nodes2 4512#usize

theorem length0 : nodes0.val.length=5216 := length _ _ (by rw [JGh_TX2_NodeViews.length0];decide)
#print axioms length0
theorem length1 : nodes1.val.length=5216 := length _ _ (by rw [JGh_TX2_NodeViews.length1];decide)
#print axioms length1
theorem length2 : nodes2.val.length=4512 := length _ _ (by rw [JGh_TX2_NodeViews.length2];decide)
#print axioms length2
end AspisR1.JGm_TX2_Supplied
end
