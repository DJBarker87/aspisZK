import NJL_OccupancyAssociation
import NIH_SelectorRow
import NFQ_StatementLaws
import NHU_Preweighted
import RPv_FIy_OccupancyRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_OccupancyParent
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIq_Native.pool_v1
abbrev Public := pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := FIq_Native.state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pair_forest_copy_terminal.Selectors
/-- K037/K038: native source order rows1017,1018, occupancy, preweighted;
SAME borrowed selectors/openings; actual full12lane argument and24reply. -/
def Cut (input output : NQ) (expected : U32) (opened : Array NQ 16#usize)
 (lanes seenLanes : Array NQ 12#usize) (reply after : Array NQ 24#usize)
 (seenInput seenOutput : NQ) (seenExpected : U32) (seenOpened : Array NQ 16#usize)
 (calls row0 row1 start : Nat) : Prop :=
 calls=4 ∧ row0=1017 ∧ row1=1018 ∧ start=0 ∧ seenInput=input ∧ seenOutput=output ∧
 seenExpected=expected ∧ seenOpened=opened ∧ seenLanes=lanes ∧ after=reply
structure Packet (packed : Array NQ 24#usize) (pub : Public) (o : Openings) (s : Selectors) where
 input : NQ
 output : NQ
 input_call : s.row 1017#usize=ok input
 output_call : s.row 1018#usize=ok output
 lanes : NJL_OccupancyPacket.Packet input output (NFQ_StatementLaws.expected pub.variant) o.z
 factored_call : NJL_OccupancyPacket.reference input output (NFQ_StatementLaws.expected pub.variant) o.z=ok (NJL_OccupancyPacket.pack lanes.last)
 literal_call : pair_forest_semantic_terminal.occupancy_lanes_literal input output (NFQ_StatementLaws.expected pub.variant) o.z=ok (NJL_OccupancyPacket.pack lanes.last)
 after : Array NQ 24#usize
 packed_call : pair_forest_semantic_terminal.add_preweighted packed 0#usize (NJL_OccupancyPacket.pack lanes.last)=ok after
 canonical : FIw_ArrayValue.canonical after
/-- Positive parent228: both CLOSED row213 domains, child244 and CLOSED230
are established on the actual source arguments and consumed internally. -/
theorem source (packed : Array NQ 24#usize) (pub : Public) (o : Openings) (s : Selectors)
 (hp : FIw_ArrayValue.canonical packed) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) (hz : FIw_ArrayValue.canonical o.z) :
 ∃ p : Packet packed pub o s,
 pair_forest_semantic_terminal.add_occupancy_lanes packed pub o s=ok p.after ∧
 Cut p.input p.output (NFQ_StatementLaws.expected pub.variant) o.z
  (NJL_OccupancyPacket.pack p.lanes.last) (NJL_OccupancyPacket.pack p.lanes.last) p.after p.after
  p.input p.output (NFQ_StatementLaws.expected pub.variant) o.z 4 1017 1018 0 := by
 obtain ⟨input,ci,hi,_⟩ := NIH_SelectorRow.result s 1017#usize (by decide) hh hl
 obtain ⟨output,co,ho,_⟩ := NIH_SelectorRow.result s 1018#usize (by decide) hh hl
 have he : (NFQ_StatementLaws.expected pub.variant).val<FIw_ScalarArithmetic.P := by
  cases pub.variant <;> decide
 obtain ⟨lanes,cl,cr,hc⟩ := NJL_OccupancyAssociation.source input output (NFQ_StatementLaws.expected pub.variant) o.z hi ho he hz
 obtain ⟨after,ca,ha,_⟩ := NHU_Preweighted.result packed 0#usize (NJL_OccupancyPacket.pack lanes.last) (by decide) (by decide) hp hc
 let p : Packet packed pub o s := ⟨input,output,ci,co,lanes,cl,cr,after,ca,ha⟩
 refine ⟨p,?_,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
 have c0 : pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW=ok 1017#usize := FIy_OccupancyRows.input
 have c1 : pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW=ok 1018#usize := FIy_OccupancyRows.output
 have expected := NFQ_StatementLaws.expected_reference pub.variant
 simp only [pair_forest_semantic_terminal.add_occupancy_lanes,c0,c1,ci,co,expected,cr,ca,bind_tc_ok]
#print Packet
#print source
#print axioms source
end AspisR1.NJL_OccupancyParent
end
