import NMX_Semantics
import NMX_DecoderLibrary
import NMX_DecoderErrors
import NMX_HeterogeneousPrimitives
set_option autoImplicit false
noncomputable section
namespace NMX_BoxCommands
open Aeneas Aeneas.Std NMX_OwnedPackets

theorem master (L : RSL.PoolLib) (owner : Nat) (b : Slice U8) :
 NMX_Heterogeneous.Refines (fun value : Box Master => NMX_Carrier.master value.payload)
  (NMX_Semantics.boxed owner (NMX_MasterValue.decoded b))
  (RSL.decodeMasterBox (NMX_DecoderLibrary.install L) (NMX_Carrier.bytes b)) := by
 unfold RSL.decodeMasterBox
 change NMX_Heterogeneous.Refines _ _
  (RSL.RS.bind (RSL.RS.ofOption (NMX_DecoderLibrary.master (NMX_Carrier.bytes b)) .invalidAccountData) _)
 rw [NMX_DecoderLibrary.master_same]
 cases decoded : NMX_MasterValue.decoded b with
 | Err e =>
   have same := NMX_DecoderErrors.master b e decoded
   subst e
   rw [RSL.RS.ofOption,RSL.RS.bind_throw]
   intro env o run
   change o = ⟨.ret (.error .invalidAccountData),[]⟩ at run
   subst o
   rfl
 | Ok value =>
   rw [RSL.RS.ofOption,RSL.RS.bind_pure]
   exact NMX_HeterogeneousPrimitives.allocation _ (⟨owner,value⟩ : Box Master)

theorem checkpoint (L : RSL.PoolLib) (owner : Nat) (b : Slice U8) :
 NMX_Heterogeneous.Refines (fun value : Box Checkpoint => NMX_Carrier.checkpoint value.payload)
  (NMX_Semantics.boxed owner (NMX_CheckpointValue.decoded b))
  (RSL.decodeCheckpointBox (NMX_DecoderLibrary.install L) (NMX_Carrier.bytes b)) := by
 unfold RSL.decodeCheckpointBox
 change NMX_Heterogeneous.Refines _ _
  (RSL.RS.bind (RSL.RS.ofOption (NMX_DecoderLibrary.checkpoint (NMX_Carrier.bytes b)) .invalidAccountData) _)
 rw [NMX_DecoderLibrary.checkpoint_same]
 cases decoded : NMX_CheckpointValue.decoded b with
 | Err e =>
   have same := NMX_DecoderErrors.checkpoint b e decoded
   subst e
   rw [RSL.RS.ofOption,RSL.RS.bind_throw]
   intro env o run
   change o = ⟨.ret (.error .invalidAccountData),[]⟩ at run
   subst o
   rfl
 | Ok value =>
   rw [RSL.RS.ofOption,RSL.RS.bind_pure]
   exact NMX_HeterogeneousPrimitives.allocation _ (⟨owner,value⟩ : Box Checkpoint)
#print axioms master
#print axioms checkpoint
end NMX_BoxCommands
end
