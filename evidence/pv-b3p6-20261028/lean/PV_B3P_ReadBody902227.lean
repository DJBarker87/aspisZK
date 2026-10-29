import PV_B3P_P227_09
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

/-- Exact emitted body context; only the immutable-read callee is abstracted. -/
def reference_terminal_absorption_lanes_literal_read_context9 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (low : aspis_core.field.QM31) (fixed : aspis_core.field.QM31)
  (chunk_two : aspis_core.field.QM31) (chunk_eight : aspis_core.field.QM31)
  (nodes : aspis_core.field.QM31)
  (openings : Array aspis_core.field.QM31 16#usize)  :
  Result (Array aspis_core.field.QM31 16#usize) :=  do
  let output := Array.repeat 16#usize aspis_core.field.QM31.ZERO
  let q ← source_read openings 0#usize
  let q1 ←
    reference_terminal.absorption_lane227 0#usize low fixed chunk_two
      chunk_eight nodes q
  let output1 ← Array.update output 0#usize q1
  let q2 ← source_read openings 1#usize
  let q3 ←
    reference_terminal.absorption_lane227 1#usize low fixed chunk_two
      chunk_eight nodes q2
  let output2 ← Array.update output1 1#usize q3
  let q4 ← source_read openings 2#usize
  let q5 ←
    reference_terminal.absorption_lane227 2#usize low fixed chunk_two
      chunk_eight nodes q4
  let output3 ← Array.update output2 2#usize q5
  let q6 ← source_read openings 3#usize
  let q7 ←
    reference_terminal.absorption_lane227 3#usize low fixed chunk_two
      chunk_eight nodes q6
  let output4 ← Array.update output3 3#usize q7
  let q8 ← source_read openings 4#usize
  let q9 ←
    reference_terminal.absorption_lane227 4#usize low fixed chunk_two
      chunk_eight nodes q8
  let output5 ← Array.update output4 4#usize q9
  let q10 ← source_read openings 5#usize
  let q11 ←
    reference_terminal.absorption_lane227 5#usize low fixed chunk_two
      chunk_eight nodes q10
  let output6 ← Array.update output5 5#usize q11
  let q12 ← source_read openings 6#usize
  let q13 ←
    reference_terminal.absorption_lane227 6#usize low fixed chunk_two
      chunk_eight nodes q12
  let output7 ← Array.update output6 6#usize q13
  let q14 ← source_read openings 7#usize
  let q15 ←
    reference_terminal.absorption_lane227 7#usize low fixed chunk_two
      chunk_eight nodes q14
  let output8 ← Array.update output7 7#usize q15
  let q16 ← source_read openings 8#usize
  let q17 ←
    reference_terminal.absorption_lane227 8#usize low fixed chunk_two
      chunk_eight nodes q16
  let output9 ← Array.update output8 8#usize q17
  let q18 ← source_read openings 9#usize
  let q19 ←
    reference_terminal.absorption_lane227 9#usize low fixed chunk_two
      chunk_eight nodes q18
  let output10 ← Array.update output9 9#usize q19
  let q20 ← source_read openings 10#usize
  let q21 ←
    reference_terminal.absorption_lane227 10#usize low fixed chunk_two
      chunk_eight nodes q20
  let output11 ← Array.update output10 10#usize q21
  let q22 ← source_read openings 11#usize
  let q23 ←
    reference_terminal.absorption_lane227 11#usize low fixed chunk_two
      chunk_eight nodes q22
  let output12 ← Array.update output11 11#usize q23
  let q24 ← source_read openings 12#usize
  let q25 ←
    reference_terminal.absorption_lane227 12#usize low fixed chunk_two
      chunk_eight nodes q24
  let output13 ← Array.update output12 12#usize q25
  let q26 ← source_read openings 13#usize
  let q27 ←
    reference_terminal.absorption_lane227 13#usize low fixed chunk_two
      chunk_eight nodes q26
  let output14 ← Array.update output13 13#usize q27
  let q28 ← source_read openings 14#usize
  let q29 ←
    reference_terminal.absorption_lane227 14#usize low fixed chunk_two
      chunk_eight nodes q28
  let output15 ← Array.update output14 14#usize q29
  let q30 ← source_read openings 15#usize
  let q31 ←
    reference_terminal.absorption_lane227 15#usize low fixed chunk_two
      chunk_eight nodes q30
  Array.update output15 15#usize q31

def reference_terminal_absorption_lanes_literal_direct_read9 (low : aspis_core.field.QM31) (fixed : aspis_core.field.QM31)
  (chunk_two : aspis_core.field.QM31) (chunk_eight : aspis_core.field.QM31)
  (nodes : aspis_core.field.QM31)
  (openings : Array aspis_core.field.QM31 16#usize)  :
  Result (Array aspis_core.field.QM31 16#usize) :=
  reference_terminal_absorption_lanes_literal_read_context9 (fun values i => Array.index_usize values i) low fixed chunk_two chunk_eight nodes openings

theorem reference_terminal_absorption_lanes_literal_read_binding9 (low : aspis_core.field.QM31) (fixed : aspis_core.field.QM31)
  (chunk_two : aspis_core.field.QM31) (chunk_eight : aspis_core.field.QM31)
  (nodes : aspis_core.field.QM31)
  (openings : Array aspis_core.field.QM31 16#usize)  :
    reference_terminal.absorption_lanes_literal low fixed chunk_two chunk_eight nodes openings = reference_terminal_absorption_lanes_literal_direct_read9 low fixed chunk_two chunk_eight nodes openings :=
  congrArg (fun source_read => reference_terminal_absorption_lanes_literal_read_context9 source_read low fixed chunk_two chunk_eight nodes openings) read_function_binding

#print axioms reference_terminal_absorption_lanes_literal_read_binding9
end PV_B3P_Binding9227
