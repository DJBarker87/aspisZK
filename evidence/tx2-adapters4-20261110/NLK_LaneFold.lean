import NLK_ParentFold
import NLA_LaneAssemble
import NKY_BoxComplete
set_option autoImplicit false
noncomputable section
namespace NLK_LaneFold
open Aeneas Aeneas.Std Result
open AspisR1
abbrev Lane := NLA_LaneAssemble.Lane
abbrev PE := NKF_BoxModel.PE
/-- One invocation's complete value Result is fed to its sole allocation site.
This is a local frame chain: it never claims arbitrary `decoded` is the native
invocation, and never turns a returning Box window into allocator totality. -/
def allocate {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (r : NP6_StdModel.Reservation) (owner : Nat)
 (decoded : Result (core.result.Result Lane PE)) :=
 NKY_BoxAction.run a s 720 r owner decoded

/-- Source errors exit before the allocation site, for EVERY reservation. -/
theorem error_before_allocation {S : Type} (a : S2W_D189Wrappers.Allocator S)
 (s : S) (r : NP6_StdModel.Reservation) (owner : Nat) (e : PE) :
 allocate a s r owner (ok (.Err e))=ok (.Err e,s) := rfl

/-- The arbitrary reservation is consumed, including exhaustion, fail and div.
The inherited allocation law carries the actual allocator post and heap frame. -/
theorem allocation_packet {S : Type} (a : S2W_D189Wrappers.Allocator S)
 (s : S) (r : NP6_StdModel.Reservation) (owner : Nat)
 (heap : NKY_BoxFrame.Heap Lane) (decoded : Result (core.result.Result Lane PE)) :
 NKY_BoxPacket.Law a s 720 8 r owner heap decoded :=
 NKY_BoxPacket.complete a s 720 8 r owner heap decoded

/-- SAME root, SAME loop state, SAME source terminal check and SAME allocation
are composed. Per-iteration native cuts remain explicit LOCAL obligations. -/
theorem source_order {S F : Type} (a : S2W_D189Wrappers.Allocator S)
 (s : S) (r : NP6_StdModel.Reservation) (owner : Nat)
 (rootReply : Result (core.result.Result NKP_LaneCuts.Node F))
 (empty : Fin 20 → NKP_LaneCuts.Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result NKP_LaneCuts.Node F)
 (step : NKP_LaneCuts.Frontier → Fin 20 → NKP_LaneCuts.Reply × NKP_LaneCuts.Frontier)
 (cuts : ∀ before level, NKP_LaneCuts.IterationCut (empty level) (occupied level) before
   (step before level).2 level (raw level) (step before level).1)
 (levels : List (Fin 20)) (before : NKP_LaneCuts.Frontier)
 (bump : U8) (master : Array U8 32#usize) (lane : U8) (next : U64)
 (emptyRoot : NKP_LaneCuts.Node) :
 allocate a s r owner
  (NLA_LaneAssemble.complete rootReply (NKP_LaneInduction.fold step levels before)
    (ok ()) bump master lane next emptyRoot) =
 allocate a s r owner
  (NLA_LaneAssemble.complete rootReply (NKF_LaneTrace.run empty occupied raw levels before)
    (ok ()) bump master lane next emptyRoot) := by
 rw [NLA_LaneAssemble.source_steps rootReply empty occupied raw step cuts levels before
      (ok ()) bump master lane next emptyRoot]

#print error_before_allocation
#print axioms error_before_allocation
#print allocation_packet
#print axioms allocation_packet
#print source_order
#print axioms source_order
end NLK_LaneFold
