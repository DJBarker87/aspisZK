import F3P_TraceInput
import F3P_TraceStart
import F3P_TraceBytes0
import F3P_TraceBytes1
import F3P_TraceBytes2
import F3P_TraceBytes3
import F3P_ListWindow
set_option autoImplicit false
namespace AspisR1.F3P_TraceWindow
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem window (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.inputBytes t).val=
      ((ParserTrace.payloadData t).val.drop ((ParserTrace.payloadStart t).val)).take 16 := by
  rw [F3P_TraceInput.bytes]
  let v : Fin 16 → U8 := ![(ParserTrace.b0 t),(ParserTrace.b1 t),(ParserTrace.b2 t),(ParserTrace.b3 t),(ParserTrace.b4 t),(ParserTrace.b5 t),(ParserTrace.b6 t),(ParserTrace.b7 t),(ParserTrace.b8 t),(ParserTrace.b9 t),(ParserTrace.b10 t),(ParserTrace.b11 t),(ParserTrace.b12 t),(ParserTrace.b13 t),(ParserTrace.b14 t),(ParserTrace.b15 t)]
  have same := F3P_ListWindow.window (ParserTrace.payloadData t).val (ParserTrace.payloadStart t).val 16 v
  have reads : ∀ i : Fin 16,
      (ParserTrace.payloadData t).val[(ParserTrace.payloadStart t).val+i.val]?=some (v i) := by
    intro i
    fin_cases i
    · exact F3P_TraceBytes0.read0 r byteOffset j offset q t
    · exact F3P_TraceBytes0.read1 r byteOffset j offset q t
    · exact F3P_TraceBytes0.read2 r byteOffset j offset q t
    · exact F3P_TraceBytes0.read3 r byteOffset j offset q t
    · exact F3P_TraceBytes1.read4 r byteOffset j offset q t
    · exact F3P_TraceBytes1.read5 r byteOffset j offset q t
    · exact F3P_TraceBytes1.read6 r byteOffset j offset q t
    · exact F3P_TraceBytes1.read7 r byteOffset j offset q t
    · exact F3P_TraceBytes2.read8 r byteOffset j offset q t
    · exact F3P_TraceBytes2.read9 r byteOffset j offset q t
    · exact F3P_TraceBytes2.read10 r byteOffset j offset q t
    · exact F3P_TraceBytes2.read11 r byteOffset j offset q t
    · exact F3P_TraceBytes3.read12 r byteOffset j offset q t
    · exact F3P_TraceBytes3.read13 r byteOffset j offset q t
    · exact F3P_TraceBytes3.read14 r byteOffset j offset q t
    · exact F3P_TraceBytes3.read15 r byteOffset j offset q t
  exact (same reads).symm

#print axioms window
end AspisR1.F3P_TraceWindow
