import WireBindingRecordCodec
import BinWireEnvelopeLengths

/-! D79 extension: typed checkpoint binding records and the admitted ASF8
account decoder. Does not assert whole-tx1 source simulation. -/
set_option autoImplicit false
namespace AspisR1.BinWireBindingLengths
open WireBindingRecordCodec
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal

/-- The first guard of candidate.rs:40, independently of the remaining parser.
It accepts every byte content of the fixed compact length. -/
def compactLengthGuard (bs : List UInt8) : Bool := bs.length == proof_bytes

theorem compact_guard_length (bs : List UInt8) (h : compactLengthGuard bs = true) :
    bs.length = 57607 := by
  have he : bs.length = proof_bytes := by simpa [compactLengthGuard] using h
  exact he.trans proof_bytes_eq

theorem compact_guard_safe (bs : List UInt8) (h : compactLengthGuard bs = true) :
    bs.length ≠ 65 ∧ bs.length ≠ 31 := by
  have hl := compact_guard_length bs h
  omega

/-- Unlike an unrestricted public argument, admitted ASF8 decoding fixes size. -/
theorem decoded_asf8_class (bs : Slice U8) (out : PoolV1PairForestTerminalStatementV1)
    (h : decode_pool_v1_pair_forest_terminal_statement_v1 bs = ok (.Ok out)) :
    bs.val.length = (Tx1Class.binding .asf8Account).size ∧
    bs.val.length ≠ 65 ∧ bs.val.length ≠ 31 := by
  have hl := BinWireEnvelopeLengths.decoded_asf8_length bs out h
  change bs.val.length = asf8_size ∧ _
  rw [asf8_size_eq]
  omega

theorem binding_ne_node (r : BindingRecord) (toByte : UInt8 → BinMerkle32Path.Byte)
    (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠ r.bytes.map toByte := by
  apply BinGrammar.node_ne_length
  simpa only [List.length_map] using (binding_safe r).1

theorem binding_ne_framed31 (r : BindingRecord) (frame : List UInt8)
    (hf : frame.length = 31) : r.bytes ≠ frame := by
  intro he
  exact (binding_safe r).2 ((congrArg List.length he).trans hf)

/-- A classified read needs no separate length-exclusion premise. Source
execution membership in the class list is the standing R-wire obligation. -/
theorem classified_ne_node (c : Tx1Class) (hn : c ≠ .binaryNode)
    (bs : List BinMerkle32Path.Byte) (hclass : bs.length = c.size)
    (cs : BinMerkle32Path.Children) : BinMerkle32Path.nodeInput cs ≠ bs := by
  apply BinGrammar.node_ne_length
  rw [hclass]
  exact (tx1_class_safe c hn).1

#print axioms compact_guard_length
#print axioms compact_guard_safe
#print axioms decoded_asf8_class
#print axioms binding_ne_node
#print axioms binding_ne_framed31
#print axioms classified_ne_node
end AspisR1.BinWireBindingLengths
