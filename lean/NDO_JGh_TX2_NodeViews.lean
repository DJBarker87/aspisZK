import JGh_TX2_SlotOffsets
import NDO_JGf_TX2_Count0
import NDO_JGf_TX2_Count2
import NDO_JGh_TX2_M1Layout
import NDO_JGf_TX2_M0Layout
import NDO_JGc_TX2_LeafHelpers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_NodeViews
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof
open JGh_TX2_SlotOffsets

theorem proof_length : JFx_NativeBytes.proof.val.length=57607 := by
  simpa only [JFx_NativeBytes.proof] using JFx_NativeBytes.proofBytes_length
#print axioms proof_length

def nodes0 : Slice U8 := MultiproofConeSlices.sub JFx_NativeBytes.proof
  (Port4B_SlotInstall.offset 3 (by decide)) (Port4B_SlotInstall.offset 4 (by decide))
def nodes1 : Slice U8 := MultiproofConeSlices.sub JFx_NativeBytes.proof
  (Port4B_SlotInstall.offset 4 (by decide)) (Port4B_SlotInstall.offset 5 (by decide))

def nodes2 : Slice U8 := MultiproofConeSlices.sub JFx_NativeBytes.proof
  (Port4B_SlotInstall.offset 5 (by decide)) (Port4B_SlotInstall.offset 6 (by decide))

theorem values0 : nodes0.val=(JFx_NativeBytes.proof.val.drop 41799).take 5504 := by
  simp only [nodes0,MultiproofConeSlices.sub,off3,off4,Nat.reduceSub]
#print axioms values0
theorem values1 : nodes1.val=(JFx_NativeBytes.proof.val.drop 47303).take 5504 := by
  simp only [nodes1,MultiproofConeSlices.sub,off4,off5,Nat.reduceSub]
#print axioms values1

theorem source0 : Port4B_Install.leaves.op3 JFx_NativeBytes.proof 3#usize=ok nodes0 := by
  rw [show Port4B_Install.leaves.op3=Port4B_SlotInstall.nodeSlot from rfl]
  rw [Port4B_SlotInstall.nodeSlot,dif_pos (by decide : (3#usize).val<6)]
  exact MultiproofConeSlices.range_total _ _ _ (by change (Port4B_SlotInstall.offset 3 (by decide)).val≤(Port4B_SlotInstall.offset 4 (by decide)).val; rw [off3,off4] <;> decide)
    (by change (Port4B_SlotInstall.offset 4 (by decide)).val≤JFx_NativeBytes.proof.val.length; rw [off4,proof_length] <;> decide)
#print axioms source0

theorem source1 : Port4B_Install.leaves.op3 JFx_NativeBytes.proof 4#usize=ok nodes1 := by
  rw [show Port4B_Install.leaves.op3=Port4B_SlotInstall.nodeSlot from rfl]
  rw [Port4B_SlotInstall.nodeSlot,dif_pos (by decide : (4#usize).val<6)]
  exact MultiproofConeSlices.range_total _ _ _ (by change (Port4B_SlotInstall.offset 4 (by decide)).val≤(Port4B_SlotInstall.offset 5 (by decide)).val; rw [off4,off5] <;> decide)
    (by change (Port4B_SlotInstall.offset 5 (by decide)).val≤JFx_NativeBytes.proof.val.length; rw [off5,proof_length] <;> decide)
#print axioms source1

theorem length0 : nodes0.val.length=5504 := by
  rw [values0,List.length_take,List.length_drop,proof_length]
  rfl
#print axioms length0

theorem length1 : nodes1.val.length=5504 := by
  rw [values1,List.length_take,List.length_drop,proof_length]
  rfl
#print axioms length1
theorem values2 : nodes2.val=(JFx_NativeBytes.proof.val.drop 52807).take 4800 := by
  simp only [nodes2,MultiproofConeSlices.sub,off5,off6,Nat.reduceSub]
#print axioms values2

theorem source2 : Port4B_Install.leaves.op3 JFx_NativeBytes.proof 5#usize=ok nodes2 := by
  rw [show Port4B_Install.leaves.op3=Port4B_SlotInstall.nodeSlot from rfl]
  rw [Port4B_SlotInstall.nodeSlot,dif_pos (by decide : (5#usize).val<6)]
  exact MultiproofConeSlices.range_total _ _ _ (by change (Port4B_SlotInstall.offset 5 (by decide)).val≤(Port4B_SlotInstall.offset 6 (by decide)).val; rw [off5,off6] <;> decide)
    (by change (Port4B_SlotInstall.offset 6 (by decide)).val≤JFx_NativeBytes.proof.val.length; rw [off6,proof_length] <;> decide)
#print axioms source2

theorem length2 : nodes2.val.length=4800 := by
  rw [values2,List.length_take,List.length_drop,proof_length]
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
