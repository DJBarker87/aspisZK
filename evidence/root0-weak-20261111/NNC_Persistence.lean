import NNC_SourceCuts
set_option autoImplicit false
noncomputable section
namespace NNC_Persistence
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
/-- The selected checkpoint getter reads the original entry buffer without
using the missing TX2 model-success field. -/
theorem checkpoint_buffer (ops : AdapterRw.Ops) (e1 e2 : Entry)
 (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts ops e1.first (e2.second secondSizes) saved f s) :
 s.checkpoint.val=(e2.buffers (e2.handles 6).1).val := by
 have same:=Result.ok.inj (cuts.checkpoint2Index.symm.trans (Hist_SecondSnapshot.second_index e2))
 have read:=cuts.checkpoint2Read
 rw [same] at read
 exact Hist_SecondSnapshot.snapshot_bytes ops e2 6 1768 1768 s.checkpoint read
/-- A nonempty native checkpoint getter proves that the selected runtime load
is live, replacing CPG_Accepted.reader_positive's extraction.stage2 use. -/
theorem reader_load {Tx A : Type} (p : CPG_Projection.Observations Tx A) (u : Tx)
 (e2 : Entry) (entry : e2=CPG_Projection.entry p u) (ck : Slice U8)
 (read : ck.val=(e2.buffers (e2.handles 6).1).val) (length : ck.val.length=1768) :
 CPG_Projection.loaded p u ((p.layout u).handles 6).1=some (bytesOf ck.val) := by
 have positive : 0<(p.bank u).lamports ((p.layout u).handles 6).1 := by
  by_contra bad
  have zero : (p.bank u).lamports ((p.layout u).handles 6).1=0 := by omega
  rw [entry] at read
  have empty:=CPG_Projection.dead p u ((p.layout u).handles 6).1 zero
  change ck.val=((CPG_Projection.entry p u).buffers ((p.layout u).handles 6).1).val at read
  rw [empty] at read
  rw [read] at length
  cases length
 have live:=CPG_Projection.live p u ((p.layout u).handles 6).1 positive
 have same:=read
 rw [entry] at same
 change ck.val=((CPG_Projection.entry p u).buffers ((p.layout u).handles 6).1).val at same
 rw [←same] at live
 exact live
/-- Native writer protection fixes the tentative DATA at the copied value.
Only the explicit approved runtime persistence item transports it to TX2.
This theorem never uses a TX2 extraction or cohort reader-success equation. -/
theorem persisted {Tx A : Type} (p : CPG_Projection.Observations Tx A) (t u : Tx)
 (ops : AdapterRw.Ops) (e1 e2 : Entry) (saved : alloc.vec.Vec U8)
 (actions : List (CPP_BankState.Action A))
 (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
 (allocator : Allocator A) (id system : S2W_ExtractionBoundary.Program)
 (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id)
 (runtime : CPR_DataPersistence.TwoTransactionLaw
  (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system)
  (CPG_Projection.before p) (CPG_Projection.tentative p)
  (CPG_Projection.success p) (CPG_Projection.loaded p))
 (eligible : CPG_Projection.ordinary p system t ((p.layout t).handles 2).1)
 (writerProtection : CPH_Protection.Facts p t saved id)
 (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts ops e1.first (e2.second secondSizes) saved f s)
 (length : s.checkpoint.val.length=1768) : bytesOf s.checkpoint.val=bytesOf saved.val := by
 have loaded:=reader_load p u e2 game.consecutive.2.2 s.checkpoint
  (checkpoint_buffer ops e1 e2 saved f s cuts) length
 rw [←game.checkpoint.1] at loaded
 have law:=runtime t u (CPH_Game.next game) ((p.layout t).handles 2).1 eligible
 rw [game.parent] at law
 simp only [↓reduceIte] at law
 have visible : some (bytesOf s.checkpoint.val)=
  CPR_DataPersistence.visible (CPG_Projection.tentative p t ((p.layout t).handles 2).1) :=
  loaded.symm.trans law
 unfold CPR_DataPersistence.visible at visible
 split at visible
 · cases visible
 · have same:=Option.some.inj visible
   have framed:=writerProtection.2.2.2.2.1
   change bytesOf s.checkpoint.val=bytesOf ((p.parentTentative t).cells ((p.layout t).handles 2).1).data.val at same
   rw [framed] at same
   exact same.trans (CPR_SourceBank.copied_data (CPG_Projection.cached (p.bank t))
    ((p.layout t).handles 2).1 saved)
#print persisted
#print axioms checkpoint_buffer
#print axioms reader_load
#print axioms persisted
end NNC_Persistence
