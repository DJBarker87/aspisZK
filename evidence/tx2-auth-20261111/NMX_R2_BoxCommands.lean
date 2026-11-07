import NMX_R2_Semantics
import NMX_R2_DecoderLibrary
import NMX_DecoderErrors
import NMX_R2_HeterogeneousPrimitives
set_option autoImplicit false
noncomputable section
namespace NMX_R2_BoxCommands
open Aeneas Aeneas.Std NMX_OwnedPackets

theorem master (L : RSL.PoolLib) (owner : Nat) (b : Slice U8) :
 NMX_R2_Heterogeneous.Refines (fun value : Box Master => NMX_R2_Carrier.master value.payload)
  (NMX_R2_Semantics.boxed owner (NMX_MasterValue.decoded b))
  (RSL.decodeMasterBox (NMX_R2_DecoderLibrary.install L) (NMX_R2_Carrier.bytes b)) := by
 unfold RSL.decodeMasterBox
 change NMX_R2_Heterogeneous.Refines _ _
  (RSL.RS.bind (RSL.RS.ofOption (NMX_R2_DecoderLibrary.master (NMX_R2_Carrier.bytes b)) .invalidAccountData) _)
 rw [NMX_R2_DecoderLibrary.master_same]
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
   exact NMX_R2_HeterogeneousPrimitives.allocation _ (⟨owner,value⟩ : Box Master)

theorem checkpoint (L : RSL.PoolLib) (owner : Nat) (b : Slice U8) :
 NMX_R2_Heterogeneous.Refines (fun value : Box Checkpoint => NMX_R2_Carrier.checkpoint value.payload)
  (NMX_R2_Semantics.boxed owner (NMX_CheckpointValue.decoded b))
  (RSL.decodeCheckpointBox (NMX_R2_DecoderLibrary.install L) (NMX_R2_Carrier.bytes b)) := by
 unfold RSL.decodeCheckpointBox
 change NMX_R2_Heterogeneous.Refines _ _
  (RSL.RS.bind (RSL.RS.ofOption (NMX_R2_DecoderLibrary.checkpoint (NMX_R2_Carrier.bytes b)) .invalidAccountData) _)
 rw [NMX_R2_DecoderLibrary.checkpoint_same]
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
   exact NMX_R2_HeterogeneousPrimitives.allocation _ (⟨owner,value⟩ : Box Checkpoint)
#print axioms master
#print axioms checkpoint
end NMX_R2_BoxCommands
end
