import F3P_SliceIndex
import F3P_TraceArithmetic
set_option autoImplicit false
namespace AspisR1.F3P_TraceBytes2
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem read8 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+8]?=some (ParserTrace.b8 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 8#usize (ParserTrace.p8 t) (ParserTrace.hp8 t)
  change (ParserTrace.p8 t).val=(ParserTrace.payloadStart t).val+8 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread8 t)
  rw [pos] at read
  exact read

#print axioms read8

theorem read9 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+9]?=some (ParserTrace.b9 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 9#usize (ParserTrace.p9 t) (ParserTrace.hp9 t)
  change (ParserTrace.p9 t).val=(ParserTrace.payloadStart t).val+9 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread9 t)
  rw [pos] at read
  exact read

#print axioms read9

theorem read10 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+10]?=some (ParserTrace.b10 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 10#usize (ParserTrace.p10 t) (ParserTrace.hp10 t)
  change (ParserTrace.p10 t).val=(ParserTrace.payloadStart t).val+10 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread10 t)
  rw [pos] at read
  exact read

#print axioms read10

theorem read11 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+11]?=some (ParserTrace.b11 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 11#usize (ParserTrace.p11 t) (ParserTrace.hp11 t)
  change (ParserTrace.p11 t).val=(ParserTrace.payloadStart t).val+11 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread11 t)
  rw [pos] at read
  exact read

#print axioms read11
end AspisR1.F3P_TraceBytes2
