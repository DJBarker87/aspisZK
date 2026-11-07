import NNC_WeakReader
import NNC_064Weak
import NNC_Persistence
set_option autoImplicit false
noncomputable section
namespace NNC_WeakExtents
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open S2W_D189Entry S2W_D189Wrappers

/-- Singleton-length deferred snapshot guard, from the SAME successful getter. -/
theorem snapshot_length (ops : AdapterRw.Ops) (e : Entry) (i n : Nat) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot i n n)=ok (.Ok bytes)) :
 bytes.val.length=n := by
 have image := Hist_SecondSnapshot.snapshot_bytes ops e i n n bytes read
 obtain ⟨copied,stored,_⟩ := S2W.SnapshotJoin.data_success ops (e.snapshot i n n) bytes read
 change (if (e.buffers (e.handles i).1).val.length=n ∨ (e.buffers (e.handles i).1).val.length=n
   then core.result.Result.Ok (e.buffers (e.handles i).1)
   else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
   core.result.Result.Ok copied at stored
 split at stored
 · rename_i size
   rw [image]
   exact size.elim id id
 · cases stored

theorem selected (ops auth : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (e : Entry) (input : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (s : SecondCut)
 (facts : NNC_WeakReader.Facts ops auth id (e.second secondSizes) input slot s) :
 s.raw.val.length=58295 ∧ s.finish.val=58295 ∧ s.checkpoint.val.length=1768 ∧
 s.proof.val.length=57607 ∧ s.pub.val.length≤1880 ∧
 s.raw.val=(e.buffers (e.handles 0).1).val ∧
 s.checkpoint.val=(e.buffers (e.handles 6).1).val := by
 have at0 : Slice.index_usize (e.second secondSizes) 0#usize=ok (e.snapshot 0 58295 58295) := rfl
 have eq0 := Result.ok.inj (facts.proofIndex.symm.trans at0)
 have eq6 := Result.ok.inj (facts.checkpointIndex.symm.trans (Hist_SecondSnapshot.second_index e))
 have read0 := facts.proofRead
 have read6 := facts.checkpointRead
 rw [eq0] at read0
 rw [eq6] at read6
 have rawLength := snapshot_length ops e 0 58295 s.raw read0
 have ckLength := snapshot_length ops e 6 1768 s.checkpoint read6
 have finish : s.finish.val=58295 := facts.length.symm.trans rawLength
 have width := (AdapterRw.Ranges.selected_exact s.raw s.proof 688#usize s.finish
   (S2X.successful_range_ordered _ _ _ _ facts.range) (by omega) facts.range).2
 have v688 : (688#usize).val=688 := by scalar_tac
 rw [finish,v688] at width
 have publicLength : s.pub.val.length≤1880 := by
   have len := s.encoded.property
   change s.encoded.val.length=1880 at len
   change s.encoded.val.length≤1880
   exact len.le
 exact ⟨rawLength,finish,ckLength,by simpa using width,publicLength,
   Hist_SecondSnapshot.snapshot_bytes ops e 0 58295 58295 s.raw read0,
   Hist_SecondSnapshot.snapshot_bytes ops e 6 1768 1768 s.checkpoint read6⟩

/-- Discharge all three064 OWN input clauses from weak native snapshots/range. -/
theorem domain {X : Type} (ops auth : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (e : Entry) (input : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (s : SecondCut)
 (facts : NNC_WeakReader.Facts ops auth id (e.second secondSizes) input slot s)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) :
 NNC_064Weak.Domain ⟨d,s.pub,s.proof,s.checkpoint,hash⟩ := by
 obtain ⟨_,_,ck,proof,pub,_,_⟩ := selected ops auth id e input slot s facts
 exact ⟨proof,ck,pub⟩

#print axioms snapshot_length
#print axioms selected
#print axioms domain
end NNC_WeakExtents
