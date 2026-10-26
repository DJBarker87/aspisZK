import F3P_SliceIndex
import F3P_TraceArithmetic
set_option autoImplicit false
namespace AspisR1.F3P_TraceBytes1
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem read4 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+4]?=some (ParserTrace.b4 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 4#usize (ParserTrace.p4 t) (ParserTrace.hp4 t)
  change (ParserTrace.p4 t).val=(ParserTrace.payloadStart t).val+4 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread4 t)
  rw [pos] at read
  exact read

#print axioms read4

theorem read5 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+5]?=some (ParserTrace.b5 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 5#usize (ParserTrace.p5 t) (ParserTrace.hp5 t)
  change (ParserTrace.p5 t).val=(ParserTrace.payloadStart t).val+5 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread5 t)
  rw [pos] at read
  exact read

#print axioms read5

theorem read6 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+6]?=some (ParserTrace.b6 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 6#usize (ParserTrace.p6 t) (ParserTrace.hp6 t)
  change (ParserTrace.p6 t).val=(ParserTrace.payloadStart t).val+6 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread6 t)
  rw [pos] at read
  exact read

#print axioms read6

theorem read7 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+7]?=some (ParserTrace.b7 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 7#usize (ParserTrace.p7 t) (ParserTrace.hp7 t)
  change (ParserTrace.p7 t).val=(ParserTrace.payloadStart t).val+7 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread7 t)
  rw [pos] at read
  exact read

#print axioms read7
end AspisR1.F3P_TraceBytes1
