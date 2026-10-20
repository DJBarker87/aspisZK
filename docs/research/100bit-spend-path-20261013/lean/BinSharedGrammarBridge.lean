import SharedBinaryRecordGrammar
import BinGrammar

/-! Equality bridge only: existing Bin proofs transport by rewriting. -/
set_option autoImplicit false
namespace AspisR1.BinSharedGrammarBridge
open BinMerkle32Path

theorem node_eq (cs : Children) : nodeInput cs = AspisR1.SharedBinaryRecordGrammar.nodeInput cs :=
  BinGrammar.nodeInput_slices cs

theorem leaf_eq (tag : Byte) (packed salt : List Byte) :
    BinMerkle32Leaf.leafInput tag packed salt = AspisR1.SharedBinaryRecordGrammar.leafInput tag packed salt := rfl

theorem class_eq (c : WireBindingRecordCodec.Tx1Class) :
    c.size = AspisR1.SharedBinaryRecordGrammar.classSize c := rfl

theorem binding_eq (r : WireBindingRecordCodec.BindingRecord) :
    r.bytes = AspisR1.SharedBinaryRecordGrammar.bindingBytes r := rfl

/-- The carrier map connects soundness bytes to the very same UInt8 grammar
used by privacy; child order and all 64 digest positions are preserved. -/
theorem node_uint8_eq (cs : Children) :
    (nodeInput cs).map (fun b => b.val.toUInt8) =
      AspisR1.SharedBinaryRecordGrammar.nodeInput (fun j i => (cs j i).val.toUInt8) := by
  rw [node_eq]
  simp [AspisR1.SharedBinaryRecordGrammar.nodeInput]
  rfl

theorem leaf_uint8_eq (tag : Byte) (packed salt : List Byte) :
    (BinMerkle32Leaf.leafInput tag packed salt).map (fun b => b.val.toUInt8) =
      AspisR1.SharedBinaryRecordGrammar.leafInput tag.val.toUInt8
        (packed.map (fun b => b.val.toUInt8)) (salt.map (fun b => b.val.toUInt8)) := by
  simp [BinMerkle32Leaf.leafInput, AspisR1.SharedBinaryRecordGrammar.leafInput]
  rfl

/-- Existing node length theorem, transported; no grammar proof repeated. -/
theorem shared_node_length (cs : Children) : (AspisR1.SharedBinaryRecordGrammar.nodeInput cs).length = 65 := by
  rw [← node_eq]
  exact nodeInput_length cs

/-- Existing tag-separation theorem transported without a new separation proof. -/
theorem shared_node_ne_leaf (cs : Children) (tag : Byte) (packed salt : List Byte) :
    AspisR1.SharedBinaryRecordGrammar.nodeInput cs ≠ AspisR1.SharedBinaryRecordGrammar.leafInput tag packed salt := by
  rw [← node_eq, ← leaf_eq]
  exact BinGrammar.node_ne_leaf cs tag packed salt

#print axioms node_uint8_eq
#print axioms leaf_uint8_eq
#print axioms node_eq
#print axioms leaf_eq
#print axioms class_eq
#print axioms binding_eq
#print axioms shared_node_length
#print axioms shared_node_ne_leaf
end AspisR1.BinSharedGrammarBridge
