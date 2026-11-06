import NJL_PathSelector
import NHU_Preweighted
import NJB_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PathParent
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIq_Native.pool_v1
open NJL_PathSelector (Selectors low)
open NJL_PathPacket (Openings)
structure Packet (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) where
 selector : NJL_PathSelector.Packet s
 lanes : NJL_PathPacket.Packet selector.selector o
 factored_call : NJL_PathPacket.reference selector.selector o=ok (NJL_PathPacket.pack lanes.after)
 literal_call : pair_forest_semantic_terminal.path_lanes_literal selector.selector o=ok (NJL_PathPacket.pack lanes.after)
 after : Array NQ 24#usize
 packed_call : pair_forest_semantic_terminal.add_preweighted packed 32#usize (NJL_PathPacket.pack lanes.after)=ok after
 canonical : FIw_ArrayValue.canonical after
/-- K041/K042: exact source range,4field operations, SAME THREE-view borrowed
Openings, full17lane packed argument and all24 returned cells. -/
def Cut (s : Selectors) (ctx : NJL_PathSelector.Packet s) (events : Fin 4 → NJB_Cuts.Event)
 (o seenOpenings : Openings) (lanes seenLanes : Array NQ 17#usize) (reply after : Array NQ 24#usize)
 (calls operations start first last : Nat) : Prop :=
 calls=3 ∧ operations=4 ∧ start=32 ∧ first=57 ∧ last=63 ∧
 events 0=⟨1,low s 1,low s 5⟩ ∧ events 1=⟨1,ctx.a,low s 9⟩ ∧
 events 2=⟨1,ctx.b,low s 13⟩ ∧ events 3=⟨0,ctx.high,ctx.c⟩ ∧
 seenOpenings=o ∧ seenLanes=lanes ∧ after=reply
/-- Positive parent229: actual sum_high/low reads/three adds/product,
child247 and CLOSED230 domains are internally discharged. -/
theorem source (packed : Array NQ 24#usize) (o : Openings) (s : Selectors)
 (hp : FIw_ArrayValue.canonical packed) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) (hz : FIw_ArrayValue.canonical o.z) (hb : FIw_ArrayValue.canonical o.succ_z) :
 ∃ p : Packet packed o s,pair_forest_semantic_terminal.add_path_lanes packed o s=ok p.after ∧
 ∃ events,Cut s p.selector events o o (NJL_PathPacket.pack p.lanes.after) (NJL_PathPacket.pack p.lanes.after)
 p.after p.after 3 4 32 57 63 := by
 obtain ⟨selector,_⟩ := NJL_PathSelector.source s hh hl
 obtain ⟨lanes,cf,cl,hc⟩ := NJL_PathAssociation.source selector.selector o selector.canonical hz hb
 obtain ⟨after,ca,ha,_⟩ := NHU_Preweighted.result packed 32#usize (NJL_PathPacket.pack lanes.after) (by decide) (by decide) hp hc
 let p : Packet packed o s := ⟨selector,lanes,cf,cl,after,ca,ha⟩
 refine ⟨p,?_,?_⟩
 swap
 · let events : Fin 4 → NJB_Cuts.Event := ![⟨1,low s 1,low s 5⟩,⟨1,selector.a,low s 9⟩,⟨1,selector.b,low s 13⟩,⟨0,selector.high,selector.c⟩]
   refine ⟨events,?_⟩
   simp [Cut,events,p]

 have r1 : Array.index_usize s.low 1#usize=ok (low s 1) := NJB_ArrayReads.read s.low 1#usize (by decide)
 have r5 : Array.index_usize s.low 5#usize=ok (low s 5) := NJB_ArrayReads.read s.low 5#usize (by decide)
 have r9 : Array.index_usize s.low 9#usize=ok (low s 9) := NJB_ArrayReads.read s.low 9#usize (by decide)
 have r13 : Array.index_usize s.low 13#usize=ok (low s 13) := NJB_ArrayReads.read s.low 13#usize (by decide)
 have rangeCall : Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [core.ops.range.Range.mk 57#usize 63#usize]))=ok NJL_PathSelector.ranges := rfl
 simp only [pair_forest_semantic_terminal.add_path_lanes,rangeCall,selector.high_call,r1,r5,r9,r13,
  selector.a_call,selector.b_call,selector.c_call,selector.product_call,cl,ca,bind_tc_ok]
 rfl
#print Packet
#print source
#print axioms source
end AspisR1.NJL_PathParent
end
