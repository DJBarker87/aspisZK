import NGR_Data
import NGR_WriterOutput
import NGR_NativeCopy
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGR_HISTORY
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames MultiproofConeCanonical
open CheckpointBytes5Writer CheckpointBytes5Effect
open S2W_EntryWriteHistory S2W_ReturnedCheckpoint

attribute [local irreducible] checkpoint

section
variable (prepared : Prepared) (accumulator : Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator) (hp hu hc : Digest)
local notation "saved" => checkpoint prepared accumulator domain hp hu hc

/-- The persistence link. `native_writer_result` is the explicitly OPEN TX1
producer: the SAME wrapper returns the deterministic KNE packet output. There
is no separately selected output or assumed post-write/load equality. SDK/std
reference validity remains explicit. Source protection/funding is the exact
CPH packet, not an inference from the data-only runtime trust item. -/
theorem saved_to_loaded {Tx A W : Type}
    (p : CPG_Projection.Observations Tx A) (t u : Tx) (e1 e2 : Entry)
    (actions : List (CPP_BankState.Action A))
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id system : S2W_ExtractionBoundary.Program)
    (data1 : Slice U8) (state1 final1 : A) (post1 : Heap (Nat → Record))
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id)
    (native_writer_result : first n1 copy allocator e1 id data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (protection : CPH_Protection.Facts p t saved id)
    (ordinary : CPG_Projection.ordinary p system t ((p.layout t).handles 2).1)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system)
      (CPG_Projection.before p) (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (w2 : W) (related2 : L.related w2 e2.heap) (valid2 : Valid e2.heap) :
    CPG_Projection.adjacent p t u ∧
    ((p.layout t).handles 2).1 = ((p.layout u).handles 6).1 ∧
    CPG_Projection.success p t = true ∧
    p.copied t = saved ∧ (saved).val.length = 1768 ∧
    CPG_Projection.loaded p u ((p.layout t).handles 2).1 = some (bytesOf (saved).val) ∧
    (e2.buffers (e2.handles 6).1).val = (saved).val ∧
    payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf (saved).val ∧
    payloadBytes encode (L.cellPayload w2 (L.accountData w2 6))
      (L.cellPayload w2 (L.accountData w2 6)).descriptor.length = bytesOf (saved).val ∧
    CPH_Trace.Facts p t u saved n1 n2 copy allocator id := by
  have size := checkpoint_length prepared accumulator domain hp hu hc
  have persisted := persisted_bytes p t u saved id system (CPH_Game.next game)
    ordinary game.parent protection RuntimePersistence
  have buffer := loaded_buffer p u ((p.layout t).handles 2).1 saved persisted
  have entryBuffer : (e2.buffers (e2.handles 6).1).val = (saved).val := by
    rw [game.consecutive.2.2]
    change ((CPG_Projection.entry p u).buffers ((p.layout u).handles 6).1).val = _
    rw [← game.checkpoint.1]
    exact buffer
  have written := native_written_bytes n1 copy std allocator e1 id data1 state1 final1
    saved post1 native_writer_result size
  have sdkBytes := native_buffer e2 L sdk w2 related2 valid2 6
  rw [entryBuffer] at sdkBytes
  exact ⟨CPH_Game.next game, game.checkpoint.1, game.parent, game.recorded.1.1,
    size, persisted, entryBuffer, written, sdkBytes, CPH_Trace.derive game⟩

#print axioms saved_to_loaded
end
end AspisR1.NGR_HISTORY
end
