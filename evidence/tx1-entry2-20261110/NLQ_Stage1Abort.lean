import NLQ_Stage1Fold
import NLQ_SnapshotPrefixes
import NLQ_ReplayAbort
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Abort
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
open AspisR1.S2W_D189Entry NLM_Snapshot
/-- First allocation failure has no owned-child/copy/cleanup suffix. The live
SDK post-state is derived from THIS attempted prefix, not an endpoint premise. -/
theorem first_fail (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (err : Error) (a1 a2 : Result Unit)
 (extent : (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 0).1)).length=58295) :
 NLQ_Stage1Fold.G e ops p d (.fail err) a1 a2 =
 let s := ready e 0 []
 ⟨.fail err,⟨{s with sdk:=acquired s 0,next:=s.next+1},none⟩,
  (allocationPrefix s 0 (.fail err)).map Event.snapshot⟩ := by
 unfold NLQ_Stage1Fold.G
 rw [NLQ_SnapshotPrefixes.first_abort e err a1 a2 extent]
 dsimp only
 rw [NLQ_ReplayAbort.allocation]
/-- Divergence preserves the identical entered prefix and live-token state. -/
theorem first_div (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (a1 a2 : Result Unit)
 (extent : (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 0).1)).length=58295) :
 NLQ_Stage1Fold.G e ops p d .div a1 a2 =
 let s := ready e 0 []
 ⟨.div,⟨{s with sdk:=acquired s 0,next:=s.next+1},none⟩,
  (allocationPrefix s 0 .div).map Event.snapshot⟩ := by
 unfold NLQ_Stage1Fold.G
 rw [NLQ_SnapshotPrefixes.first_diverge e a1 a2 extent]
 dsimp only
 rw [NLQ_ReplayAbort.allocation]
#print first_fail
#print first_div
#print axioms first_fail
#print axioms first_div
end NLQ_Stage1Abort
