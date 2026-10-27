import JGf_TX2_Count0
import JGf_TX2_Count2
import JGh_TX2_M1Layout
import JGf_TX2_M0Layout
import JGc_TX2_LeafHelpers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_NodeViews
open Aeneas Aeneas.Std Result

def nodes0 : Slice U8 := MultiproofConeSlices.sub JFx_NativeBytes.proof
  (Port4B_SlotInstall.offset 3 (by decide)) (Port4B_SlotInstall.offset 4 (by decide))
def nodes1 : Slice U8 := MultiproofConeSlices.sub JFx_NativeBytes.proof
  (Port4B_SlotInstall.offset 4 (by decide)) (Port4B_SlotInstall.offset 5 (by decide))

def nodes2 : Slice U8 := MultiproofConeSlices.sub JFx_NativeBytes.proof
  (Port4B_SlotInstall.offset 5 (by decide)) (Port4B_SlotInstall.offset 6 (by decide))

theorem values0 : nodes0.val=(JFx_NativeBytes.proof.val.drop 41799).take 5504 := rfl
#print axioms values0
theorem values1 : nodes1.val=(JFx_NativeBytes.proof.val.drop 47303).take 5504 := rfl
#print axioms values1

theorem source0 : Port4B_Install.leaves.op3 JFx_NativeBytes.proof 3#usize=ok nodes0 := by
  change Port4B_SlotInstall.nodeSlot _ _=_
  rw [Port4B_SlotInstall.nodeSlot,dif_pos (by decide : (3#usize).val<6)]
  exact MultiproofConeSlices.range_total _ _ _ (by decide)
    (by rw [JFx_NativeBytes.proofBytes_length];decide)
#print axioms source0

theorem source1 : Port4B_Install.leaves.op3 JFx_NativeBytes.proof 4#usize=ok nodes1 := by
  change Port4B_SlotInstall.nodeSlot _ _=_
  rw [Port4B_SlotInstall.nodeSlot,dif_pos (by decide : (4#usize).val<6)]
  exact MultiproofConeSlices.range_total _ _ _ (by decide)
    (by rw [JFx_NativeBytes.proofBytes_length];decide)
#print axioms source1

theorem length0 : nodes0.val.length=5504 := by
  rw [values0,List.length_take,List.length_drop,JFx_NativeBytes.proofBytes_length]
  rfl
#print axioms length0

theorem length1 : nodes1.val.length=5504 := by
  rw [values1,List.length_take,List.length_drop,JFx_NativeBytes.proofBytes_length]
  rfl
#print axioms length1
theorem values2 : nodes2.val=(JFx_NativeBytes.proof.val.drop 52807).take 4800 := rfl
#print axioms values2

theorem source2 : Port4B_Install.leaves.op3 JFx_NativeBytes.proof 5#usize=ok nodes2 := by
  change Port4B_SlotInstall.nodeSlot _ _=_
  rw [Port4B_SlotInstall.nodeSlot,dif_pos (by decide : (5#usize).val<6)]
  exact MultiproofConeSlices.range_total _ _ _ (by decide)
    (by rw [JFx_NativeBytes.proofBytes_length];decide)
#print axioms source2

theorem length2 : nodes2.val.length=4800 := by
  rw [values2,List.length_take,List.length_drop,JFx_NativeBytes.proofBytes_length]
  rfl
#print axioms length2
@[irreducible] def readCell (nodes : Slice U8) (cursor : Nat) : AspisV8R19.SourceDuplexStep.State :=
  fun i => AspisV8R19.SqueezeOracleBridge.decodeByte
    (((nodes.val.drop (32*cursor)).take 32).getD i.val 0#u8)

theorem read_selected (nodes : Slice U8) (cursor : Nat) (a : Array U8 32#usize)
    (selected : (nodes.val.drop (32*cursor)).take 32=a.val) :
    readCell nodes cursor=AspisV8R19.SqueezeOracleBridge.decodeState a := by
  unfold readCell
  rw [selected]
  funext i
  rw [List.getD_eq_getElem _ _ (show i.val<a.val.length by rw [a.property];exact i.isLt)]
  rfl
#print axioms read_selected
end AspisR1.JGh_TX2_NodeViews
end
