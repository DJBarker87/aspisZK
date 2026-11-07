import NNC_ByteCarriers
import NMV_RslSnapshots
set_option autoImplicit false
noncomputable section
namespace NNC_SnapshotRep
open Aeneas Aeneas.Std AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The CLOSED snapshot law's SAME entry-state origin, reused from NMV's
committed canonical transcription proof (source/object hashes are pinned). -/
theorem snapshot_origin (a : RSL.AccountInfo) (l1 l2 : Nat)
 (entry post : RSL.SdkState) (owned : RSL.OwnedAccount)
 (env : RSL.Env) (events : List RSL.Event)
 (snapshot : RSL.snapshot a l1 l2 entry env ⟨.ret (owned,post),events⟩)
 (bytes : RSL.Bytes) (read : owned.bytes=.ok bytes) : bytes=RSL.payload a entry :=
 (NMV_RslLaws.snapshot_facts a l1 l2 entry post owned env events snapshot).origin bytes read
/-- For an actual seven-snapshot sequence, lookups retain index identity,
including the checkpoint's index6, and refer to payloads BEFORE snapshots. -/
theorem images_origin (accounts : List RSL.AccountInfo) (entry post : RSL.SdkState)
 (owned : List RSL.OwnedAccount) (env : RSL.Env) (events : List RSL.Event)
 (snapshot : RSL.TX2_240.snapAll accounts RSL.TX2_240.snapLens entry env ⟨.ret (owned,post),events⟩)
 (i : Nat) (a : RSL.AccountInfo) (x : RSL.OwnedAccount)
 (atAccount : accounts[i]?=some a) (atOwned : owned[i]?=some x)
 (bytes : RSL.Bytes) (read : x.bytes=.ok bytes) : bytes=RSL.payload a entry := by
 have images:=(NMV_RslSnapshots.snapAll_facts accounts RSL.TX2_240.snapLens entry post owned env events snapshot).2
 obtain ⟨a',lens,atAccount',_,image⟩:=NMV_RslSnapshots.images_lookup entry accounts
  RSL.TX2_240.snapLens owned images i x atOwned
 have same:=Option.some.inj (atAccount'.symm.trans atAccount)
 subst a'
 exact image.origin bytes read
/-- R0-rep on native byte carriers. The three equations are consequences of
SAME snapshot images and the selected suffix; no Root0 is an input. -/
theorem at_entry (s : SecondCut) (entry : RSL.SdkState)
 (a0 a6 : RSL.AccountInfo) (pr ck : RSL.Bytes)
 (checkpointRead : NNC_ByteCarriers.host s.checkpoint.val=ck)
 (proofRead : NNC_ByteCarriers.host s.raw.val=pr)
 (checkpointOrigin : ck=RSL.payload a6 entry) (proofOrigin : pr=RSL.payload a0 entry)
 (range : s.proof.val=(s.raw.val.drop 688).take (58295-688)) :
 bytesOf s.checkpoint.val=NNC_ByteCarriers.protocol (RSL.payload a6 entry) ∧
 bytesOf s.proof.val=NNC_ByteCarriers.protocol
  (RSL.slice (RSL.payload a0 entry) 688 58295) ∧
 (NNC_ByteCarriers.Root0 (RSL.payload a6 entry)
   (RSL.slice (RSL.payload a0 entry) 688 58295) ↔ NLP_InputDomain.Root0 s.checkpoint s.proof) := by
 have hc : NNC_ByteCarriers.host s.checkpoint.val=RSL.payload a6 entry := checkpointRead.trans checkpointOrigin
 have hp : NNC_ByteCarriers.host s.proof.val=RSL.slice (RSL.payload a0 entry) 688 58295 := by
  rw [range,NNC_ByteCarriers.host_slice,proofRead,proofOrigin]
 refine ⟨?_,?_,NNC_ByteCarriers.root0_protocol s.checkpoint s.proof _ _ hc hp⟩
 · rw [←hc,NNC_ByteCarriers.protocol_host]
 · rw [←hp,NNC_ByteCarriers.protocol_host]
/-- Native selected range produces the exact RSL suffix at the original
58295-byte proof image; representation is by bytes, never by hash equality. -/
theorem selected_range (s : SecondCut)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  s.raw {start:=688#usize,«end»:=s.finish}=Aeneas.Std.Result.ok s.proof)
 (finish : s.finish.val=58295) (length : s.raw.val.length=58295) :
 s.proof.val=(s.raw.val.drop 688).take (58295-688) := by
 have selected:=AdapterRw.Ranges.selected_exact s.raw s.proof 688#usize s.finish
  (by change 688≤s.finish.val;omega) (by change s.finish.val≤s.raw.val.length;omega) range
 have v688 : (688#usize).val=688 := by scalar_tac
 simpa only [finish,v688] using selected.1
/-- Complete representation fold over the seven canonical snapshots and the
native selected range. Account descriptor association is explicit at0/6. -/
theorem from_snapshots (s : SecondCut) (accounts : List RSL.AccountInfo)
 (entry post : RSL.SdkState) (owned : List RSL.OwnedAccount)
 (env : RSL.Env) (events : List RSL.Event)
 (snapshots : RSL.TX2_240.snapAll accounts RSL.TX2_240.snapLens entry env ⟨.ret (owned,post),events⟩)
 (a0 a6 : RSL.AccountInfo) (x0 x6 : RSL.OwnedAccount)
 (at0 : accounts[0]?=some a0) (at6 : accounts[6]?=some a6)
 (owned0 : owned[0]?=some x0) (owned6 : owned[6]?=some x6)
 (read0 : x0.bytes=.ok (NNC_ByteCarriers.host s.raw.val))
 (read6 : x6.bytes=.ok (NNC_ByteCarriers.host s.checkpoint.val))
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  s.raw {start:=688#usize,«end»:=s.finish}=Aeneas.Std.Result.ok s.proof)
 (finish : s.finish.val=58295) (length : s.raw.val.length=58295) :
 bytesOf s.checkpoint.val=NNC_ByteCarriers.protocol (RSL.payload a6 entry) ∧
 bytesOf s.proof.val=NNC_ByteCarriers.protocol
  (RSL.slice (RSL.payload a0 entry) 688 58295) ∧
 (NNC_ByteCarriers.Root0 (RSL.payload a6 entry)
   (RSL.slice (RSL.payload a0 entry) 688 58295) ↔ NLP_InputDomain.Root0 s.checkpoint s.proof) := by
 have cp:=images_origin accounts entry post owned env events snapshots 6 a6 x6 at6 owned6 _ read6
 have pr:=images_origin accounts entry post owned env events snapshots 0 a0 x0 at0 owned0 _ read0
 exact at_entry s entry a0 a6 _ _ rfl rfl cp pr (selected_range s range finish length)
#print from_snapshots
#print axioms from_snapshots
#print axioms snapshot_origin
#print axioms images_origin
#print axioms at_entry
#print axioms selected_range
end NNC_SnapshotRep
