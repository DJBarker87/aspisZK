import NFB_NMFBHost
import NNC_WeakExtents
import NNC_SnapshotRep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_RootImage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_NativeConsolidation NNH_HostCtx NNH_LiteralHost
open MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- NNH source-cut fields alone identify the selected entry buffers. -/
theorem at_entry (ops : AdapterRw.Ops) (e1 e2 : Entry)
 (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts ops e1.first (e2.second secondSizes) saved f s) :
 NNC_ByteCarriers.Root0
  (S2W_ReturnedCheckpoint.nativeBytes (e2.buffers (e2.handles 6).1))
  (RSL.slice (S2W_ReturnedCheckpoint.nativeBytes (e2.buffers (e2.handles 0).1)) 688 58295) ↔
 NLP_InputDomain.Root0 s.checkpoint s.proof := by
 have at0 : Slice.index_usize (e2.second secondSizes) 0#usize = .ok (e2.snapshot 0 58295 58295) := rfl
 have eq0 := Result.ok.inj (cuts.proof2Index.symm.trans at0)
 have eq6 := Result.ok.inj (cuts.checkpoint2Index.symm.trans (Hist_SecondSnapshot.second_index e2))
 have read0 := cuts.proof2Read
 have read6 := cuts.checkpoint2Read
 rw [eq0] at read0
 rw [eq6] at read6
 have rawLen := NNC_WeakExtents.snapshot_length ops e2 0 58295 s.raw read0
 have rawImage := Hist_SecondSnapshot.snapshot_bytes ops e2 0 58295 58295 s.raw read0
 have ckImage := Hist_SecondSnapshot.snapshot_bytes ops e2 6 1768 1768 s.checkpoint read6
 have hostBytes (bytes : Slice U8) : NNC_ByteCarriers.host bytes.val = S2W_ReturnedCheckpoint.nativeBytes bytes := by
  unfold NNC_ByteCarriers.host S2W_ReturnedCheckpoint.nativeBytes
  apply List.map_congr_left
  intro byte _
  apply UInt8.toNat.inj
  change byte.val = (UInt8.ofNat byte.val).toNat
  exact (UInt8.toNat_ofNat_of_lt' byte.bv.isLt).symm
 have cp : NNC_ByteCarriers.host s.checkpoint.val = S2W_ReturnedCheckpoint.nativeBytes (e2.buffers (e2.handles 6).1) := by
  rw [ckImage]
  exact hostBytes _
 have pr : NNC_ByteCarriers.host s.proof.val = RSL.slice
  (S2W_ReturnedCheckpoint.nativeBytes (e2.buffers (e2.handles 0).1)) 688 58295 := by
  rw [NNC_SnapshotRep.selected_range s cuts.secondRange (cuts.raw2Length.symm.trans rawLen) rawLen,
   NNC_ByteCarriers.host_slice,rawImage,hostBytes]
 exact NNC_ByteCarriers.root0_protocol s.checkpoint s.proof _ _ cp pr

theorem M3 {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) : NFB_NMFBHost.M3 (Tx := Tx) L0 copy std := by
 intro c f s cuts root
 exact (at_entry (sdk c) c.i.entry c.j.entry c.world.saved f s cuts).mpr root
#print axioms at_entry
#print axioms M3
end AspisR1.NNR_RootImage
end
