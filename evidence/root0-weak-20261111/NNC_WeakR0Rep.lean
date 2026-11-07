import NNC_WeakExtents
import NNC_SnapshotRep
import NNE_Entry
set_option autoImplicit false
noncomputable section
namespace NNC_WeakR0Rep
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open S2W_D189Entry S2W_D189Wrappers

/-- Concrete NNE entry-state images, at the SAME native weak-parent cut.
The CLOSED snapshot/getter and range laws determine both original buffers.
No caller image equality, Root0 or model2 acceptance is a premise. -/
theorem at_entry (ops auth : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (e : Entry) (input : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (s : SecondCut)
 (facts : NNC_WeakReader.Facts ops auth id (e.second secondSizes) input slot s) (nonce : Nat) :
 bytesOf s.checkpoint.val=NNC_ByteCarriers.protocol
   (RSL.payload (NNE_Entry.account e 6) (NNE_Entry.state e nonce)) ∧
 bytesOf s.proof.val=NNC_ByteCarriers.protocol
   (RSL.slice (RSL.payload (NNE_Entry.account e 0) (NNE_Entry.state e nonce)) 688 58295) ∧
 (NNC_ByteCarriers.Root0
   (RSL.payload (NNE_Entry.account e 6) (NNE_Entry.state e nonce))
   (RSL.slice (RSL.payload (NNE_Entry.account e 0) (NNE_Entry.state e nonce)) 688 58295) ↔
   NLP_InputDomain.Root0 s.checkpoint s.proof) := by
 have hostBytes (bytes : Slice U8) : NNC_ByteCarriers.host bytes.val=
     S2W_ReturnedCheckpoint.nativeBytes bytes := by
   unfold NNC_ByteCarriers.host S2W_ReturnedCheckpoint.nativeBytes
   apply List.map_congr_left
   intro byte _
   apply UInt8.toNat.inj
   change byte.val=(UInt8.ofNat byte.val).toNat
   exact (UInt8.toNat_ofNat_of_lt' byte.bv.isLt).symm
 obtain ⟨rawLength,finish,_,_,_,rawImage,ckImage⟩ :=
   NNC_WeakExtents.selected ops auth id e input slot s facts
 have cp : NNC_ByteCarriers.host s.checkpoint.val=
     RSL.payload (NNE_Entry.account e 6) (NNE_Entry.state e nonce) := by
   rw [NNE_Entry.payload,ckImage]
   exact hostBytes _
 have pr : NNC_ByteCarriers.host s.raw.val=
     RSL.payload (NNE_Entry.account e 0) (NNE_Entry.state e nonce) := by
   rw [NNE_Entry.payload,rawImage]
   exact hostBytes _
 exact NNC_SnapshotRep.at_entry s (NNE_Entry.state e nonce)
   (NNE_Entry.account e 0) (NNE_Entry.account e 6) _ _ rfl rfl cp pr
   (NNC_SnapshotRep.selected_range s facts.range finish rawLength)

#print axioms at_entry
end NNC_WeakR0Rep
