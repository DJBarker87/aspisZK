import F3P_SliceIndex
import F3P_TraceArithmetic
set_option autoImplicit false
namespace AspisR1.F3P_TraceBytes3
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem read12 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+12]?=some (ParserTrace.b12 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 12#usize (ParserTrace.p12 t) (ParserTrace.hp12 t)
  change (ParserTrace.p12 t).val=(ParserTrace.payloadStart t).val+12 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread12 t)
  rw [pos] at read
  exact read

#print axioms read12

theorem read13 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+13]?=some (ParserTrace.b13 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 13#usize (ParserTrace.p13 t) (ParserTrace.hp13 t)
  change (ParserTrace.p13 t).val=(ParserTrace.payloadStart t).val+13 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread13 t)
  rw [pos] at read
  exact read

#print axioms read13

theorem read14 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+14]?=some (ParserTrace.b14 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 14#usize (ParserTrace.p14 t) (ParserTrace.hp14 t)
  change (ParserTrace.p14 t).val=(ParserTrace.payloadStart t).val+14 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread14 t)
  rw [pos] at read
  exact read

#print axioms read14

theorem read15 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+15]?=some (ParserTrace.b15 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 15#usize (ParserTrace.p15 t) (ParserTrace.hp15 t)
  change (ParserTrace.p15 t).val=(ParserTrace.payloadStart t).val+15 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread15 t)
  rw [pos] at read
  exact read

#print axioms read15
end AspisR1.F3P_TraceBytes3
