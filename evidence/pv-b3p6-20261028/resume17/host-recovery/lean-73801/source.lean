import PV_B3P_AbsorptionSource15227
namespace PV_B3P_227
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

def host_terminal.absorption_lanes_literal_loop.body
  (low : aspis_core.field.QM31) (fixed : aspis_core.field.QM31)
  (chunk_two : aspis_core.field.QM31) (chunk_eight : aspis_core.field.QM31)
  (nodes : aspis_core.field.QM31)
  (openings : Array aspis_core.field.QM31 16#usize)
  (output : Array aspis_core.field.QM31 16#usize) (lane : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 16#usize) × Std.Usize)
    (Array aspis_core.field.QM31 16#usize))
  := do
  if lane < 16#usize
  then
    let blocks ←
      if lane < 2#usize
      then ok fixed
      else
        do
        let i ← (Result.ok aspis_statement.poseidon2.RATE)
        if lane < i
        then aspis_core.field.QM31.add fixed chunk_two
        else
          let q ← aspis_core.field.QM31.add fixed chunk_two
          let q1 ← aspis_core.field.QM31.add q chunk_eight
          aspis_core.field.QM31.add q1 nodes
    let q ← aspis_core.field.QM31.mul low blocks
    let q1 ← Array.index_usize openings lane
    let q2 ← aspis_core.field.QM31.mul q q1
    let output1 ← Array.update output lane q2
    let lane1 ← lift (Std.Usize.wrapping_add lane 1#usize)
    ok (cont (output1, lane1))
  else ok (done output)

def host_terminal.absorption_lanes_literal_loop
  (low : aspis_core.field.QM31) (fixed : aspis_core.field.QM31)
  (chunk_two : aspis_core.field.QM31) (chunk_eight : aspis_core.field.QM31)
  (nodes : aspis_core.field.QM31)
  (openings : Array aspis_core.field.QM31 16#usize)
  (output : Array aspis_core.field.QM31 16#usize) (lane : Std.Usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (output1, lane1) => host_terminal.absorption_lanes_literal_loop.body
      low fixed chunk_two chunk_eight nodes openings output1 lane1)
    (output, lane)

def host_terminal.absorption_lanes_literal
  (low : aspis_core.field.QM31) (fixed : aspis_core.field.QM31)
  (chunk_two : aspis_core.field.QM31) (chunk_eight : aspis_core.field.QM31)
  (nodes : aspis_core.field.QM31)
  (openings : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let output := Array.repeat 16#usize aspis_core.field.QM31.ZERO
  host_terminal.absorption_lanes_literal_loop low fixed chunk_two chunk_eight
    nodes openings output 0#usize
end PV_B3P_227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Native15227 Result
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul Array.update

theorem absorption_body17 (low fixed two eight nodes : aspis_core.field.QM31)
    (opened output : Array aspis_core.field.QM31 16#usize) (lane : Usize) :
    host_terminal.absorption_lanes_literal_loop.body low fixed two eight nodes opened output lane =
      usize_body (absorption_source_step15 low fixed two eight nodes opened) 16#usize (output,lane) := by
  by_cases h : lane < 16#usize <;> by_cases h2 : lane < 2#usize <;>
    by_cases hrate : lane < aspis_statement.poseidon2.RATE <;>
    simp only [host_terminal.absorption_lanes_literal_loop.body,usize_body,
      absorption_source_step15,absorption_native_value15,h,h2,hrate,
      if_true,if_false,bind_tc_ok,PV_B3P_Ordered227.bind_assoc]

theorem absorption_loop17 (low fixed two eight nodes : aspis_core.field.QM31)
    (opened output : Array aspis_core.field.QM31 16#usize) (lane : Usize) :
    host_terminal.absorption_lanes_literal_loop low fixed two eight nodes opened output lane =
      loop (usize_body (absorption_source_step15 low fixed two eight nodes opened) 16#usize) (output,lane) := by
  unfold host_terminal.absorption_lanes_literal_loop
  have same : (fun (state : Array aspis_core.field.QM31 16#usize × Usize) =>
      host_terminal.absorption_lanes_literal_loop.body low fixed two eight nodes opened state.1 state.2) =
      usize_body (absorption_source_step15 low fixed two eight nodes opened) 16#usize := by
    funext state
    exact absorption_body17 low fixed two eight nodes opened state.1 state.2
  rw [same]

theorem absorption_extraction_reference17 (low fixed two eight nodes : aspis_core.field.QM31)
    (opened : Array aspis_core.field.QM31 16#usize) :
    host_terminal.absorption_lanes_literal low fixed two eight nodes opened =
      reference_terminal.absorption_lanes_literal low fixed two eight nodes opened := by
  apply Eq.trans _ (absorption_source_binding15 low fixed two eight nodes opened)
  unfold host_terminal.absorption_lanes_literal absorption_source15
  exact absorption_loop17 low fixed two eight nodes opened _ _
#print axioms absorption_body17
#print axioms absorption_loop17
#print axioms absorption_extraction_reference17
end PV_B3P_Direct17227
