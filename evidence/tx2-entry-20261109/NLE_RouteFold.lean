import NLE_EntryFold
import NIV_ForwardPacket
set_option autoImplicit false
noncomputable section
namespace NLE_RouteFold
open Aeneas Aeneas.Std Result AspisR1
/-- The four actual ASQ8 bytes exclude both stage1 instructions. -/
theorem asq8_route (data : Slice U8) (header : Hiq_ReleaseRoute.asq8 data) :
 Hiq_ReleaseRoute.route data = .second := by
 apply (Hiq_ReleaseRoute.second_iff data).mpr
 refine ⟨?_,header⟩
 intro first
 rcases first with ten | eleven
 · simp [Hiq_ReleaseRoute.asq8,ten] at header
 · simp [Hiq_ReleaseRoute.asq8,eleven] at header
/-- Full Result of the entry is the SAME stage2 child on original descriptors,
without lifecycle or stage1 hypotheses. No accepted-child premise. -/
theorem entry {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
 (state : NLE_Dispatch.State Account) (header : Hiq_ReleaseRoute.asq8 state.data) :
 (NLE_Entry.G (NIV_RawBoundary.profile ops) state).2 =
 ops.second state.program state.accounts state.data := by
 rw [NLE_Entry.emitted,NIV_ExtractedForward.forwarding,asq8_route state.data header]
/-- Complete child state/effects packet remains an explicit intermediate
parameter. Neither a successful endpoint nor a separately selected trace is
assumed: the predecessor's run computes the selected child's whole reply. -/
theorem child_packet {Account State Event : Type}
 (children : NGL_EntryRouting.Children Account State Event) (state : State)
 (program : Hiq_DispatchSource.Key) (accounts : Slice Account) (data : Slice U8)
 (header : Hiq_ReleaseRoute.asq8 data) :
 NGL_EntryRouting.run children program accounts data state =
 (children.second program accounts data state,[.second program accounts data]) :=
 NIV_ForwardPacket.second children state program accounts data (asq8_route data header)
#print asq8_route
#print entry
#print child_packet
#print axioms asq8_route
#print axioms entry
#print axioms child_packet
end NLE_RouteFold
