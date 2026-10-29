import PV_B3P_AbsorptionStep15227
import PV_B3P_SelectIndex227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def absorption_native_value15 (lane : Usize) (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31)
    (openings : Array aspis_core.field.QM31 16#usize) : Result aspis_core.field.QM31 := do
  let blocks ← if lane < 2#usize then .ok fixed
    else if lane < aspis_statement.poseidon2.RATE then aspis_core.field.QM31.add fixed chunk_two
    else do
      let a ← aspis_core.field.QM31.add fixed chunk_two
      let b ← aspis_core.field.QM31.add a chunk_eight
      aspis_core.field.QM31.add b nodes
  let scaled ← aspis_core.field.QM31.mul low blocks
  let opened ← Array.index_usize openings lane
  aspis_core.field.QM31.mul scaled opened

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul Array.update

theorem absorption_native_value_binding15 (lane : Usize) (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31)
    (openings : Array aspis_core.field.QM31 16#usize) (bound : lane.val < 16) :
    absorption_native_value15 lane low fixed chunk_two chunk_eight nodes openings =
      (do let opened ← reference_terminal.read227 openings lane
          reference_terminal.absorption_lane227 lane low fixed chunk_two chunk_eight nodes opened) := by
  have read := PV_B3P_SelectIndex227.index_value openings lane bound
  simp only [absorption_native_value15,reference_terminal.read227,
    reference_terminal.absorption_lane227,read,bind_tc_ok,PV_B3P_Ordered227.bind_assoc]
#print axioms absorption_native_value_binding15
end PV_B3P_Native15227
