import F3P_SliceIndex
import F3P_TraceArithmetic
set_option autoImplicit false
namespace AspisR1.F3P_TraceBytes0
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem read0 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+0]?=some (ParserTrace.b0 t) := by
  simpa only [Nat.add_zero] using F3P_SliceIndex.read _ _ _ (ParserTrace.hread0 t)

#print axioms read0

theorem read1 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+1]?=some (ParserTrace.b1 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 1#usize (ParserTrace.p1 t) (ParserTrace.hp1 t)
  change (ParserTrace.p1 t).val=(ParserTrace.payloadStart t).val+1 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread1 t)
  rw [pos] at read
  exact read

#print axioms read1

theorem read2 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+2]?=some (ParserTrace.b2 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 2#usize (ParserTrace.p2 t) (ParserTrace.hp2 t)
  change (ParserTrace.p2 t).val=(ParserTrace.payloadStart t).val+2 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread2 t)
  rw [pos] at read
  exact read

#print axioms read2

theorem read3 (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+3]?=some (ParserTrace.b3 t) := by
  have pos := F3P_TraceArithmetic.checked_add (ParserTrace.payloadStart t) 3#usize (ParserTrace.p3 t) (ParserTrace.hp3 t)
  change (ParserTrace.p3 t).val=(ParserTrace.payloadStart t).val+3 at pos
  have read := F3P_SliceIndex.read _ _ _ (ParserTrace.hread3 t)
  rw [pos] at read
  exact read

#print axioms read3
end AspisR1.F3P_TraceBytes0
