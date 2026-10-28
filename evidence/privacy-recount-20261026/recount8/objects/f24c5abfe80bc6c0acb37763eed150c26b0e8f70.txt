import SharedBinaryRecordGrammar
import R1Z.WireBindingLengthsR1PBin

/-! Equality bridge for the frozen privacy definitions; length/separation
proofs below are transported from the existing privacy theorems. -/
set_option autoImplicit false
namespace R1Z.SharedGrammarBridgeBin
open R0Z.FsStatement R1Z.LensR1 R1Z.TranscriptR1
open GamesR1PBin LayoutR1PBin

theorem node_eq (rest : RIdx → OracleAnswer) (ch : Fin 2 → RIdx) :
    nodeBytes rest ch = AspisR1.SharedBinaryRecordGrammar.nodeInput (fun j => rest (ch j)) := rfl

theorem treeTag_eq : treeTag = AspisR1.SharedBinaryRecordGrammar.treeTag := rfl

theorem leaf_eq (tag : UInt8) (packed : List UInt8) (salt : OracleAnswer) :
    [0x10, tag] ++ packed ++ ans salt = AspisR1.SharedBinaryRecordGrammar.leafInput tag packed (ans salt) := by
  simp only [AspisR1.SharedBinaryRecordGrammar.leafInput, List.cons_append, List.nil_append, List.append_assoc]

theorem semanticSize_eq : WireLengthsR1PBin.semanticSize = AspisR1.SharedBinaryRecordGrammar.semanticSize := rfl
theorem semanticTag_eq : WireLengthsR1PBin.semanticTag = AspisR1.SharedBinaryRecordGrammar.semanticTag := rfl
theorem openingSize_eq : WireLengthsR1PBin.openingSize = AspisR1.SharedBinaryRecordGrammar.openingSize := rfl

def toShared (w : WireLengthsR1PBin.Wire) : AspisR1.SharedBinaryRecordGrammar.Wire :=
  ⟨w.semantic, w.opening, w.final, w.publicBytes, w.tag⟩
def fromShared (w : AspisR1.SharedBinaryRecordGrammar.Wire) : WireLengthsR1PBin.Wire :=
  ⟨w.semantic, w.opening, w.final, w.publicBytes, w.tag⟩

theorem wire_roundtrip (w : WireLengthsR1PBin.Wire) : fromShared (toShared w) = w := rfl
theorem shared_roundtrip (w : AspisR1.SharedBinaryRecordGrammar.Wire) : toShared (fromShared w) = w := rfl

theorem framed_eq (w : WireLengthsR1PBin.Wire) (i : Fin 27) :
    WireLengthsR1PBin.framed w i = AspisR1.SharedBinaryRecordGrammar.framed (toShared w) i := rfl

theorem class_eq (c : AspisR1.WireBindingRecordCodec.Tx1Class) :
    c.size = AspisR1.SharedBinaryRecordGrammar.classSize c := rfl

theorem shared_framed_safe (w : AspisR1.SharedBinaryRecordGrammar.Wire) (i : Fin 27) :
    (AspisR1.SharedBinaryRecordGrammar.framed w i).length ≠ 31 ∧ (AspisR1.SharedBinaryRecordGrammar.framed w i).length ≠ 65 :=
  WireLengthsR1PBin.framed_safe (fromShared w) i

theorem shared_node_ne_binding (rest : RIdx → OracleAnswer) (ch : Fin 2 → RIdx)
    (r : AspisR1.SharedBinaryRecordGrammar.BindingRecord) : AspisR1.SharedBinaryRecordGrammar.nodeInput (fun j => rest (ch j)) ≠ AspisR1.SharedBinaryRecordGrammar.bindingBytes r := by
  rw [← node_eq]
  exact WireBindingLengthsR1PBin.node_ne_binding rest ch r

#print axioms node_eq
#print axioms treeTag_eq
#print axioms leaf_eq
#print axioms semanticSize_eq
#print axioms semanticTag_eq
#print axioms openingSize_eq
#print axioms wire_roundtrip
#print axioms shared_roundtrip
#print axioms framed_eq
#print axioms class_eq
#print axioms shared_framed_safe
#print axioms shared_node_ne_binding
end R1Z.SharedGrammarBridgeBin
