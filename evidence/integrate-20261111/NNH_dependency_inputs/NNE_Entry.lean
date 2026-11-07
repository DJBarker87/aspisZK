import S2W_D189Consolidation
import NNE_SdkState
set_option autoImplicit false
noncomputable section
namespace NNE_Entry
open Aeneas Aeneas.Std AspisR1 S2W_D189Entry S2W_ReturnedCheckpoint S2Trust S2W_EntryWriteHistory

def key (k : AdapterRw.solana_pubkey.Pubkey) : RSL.B32 :=
 ⟨k.val.map nativeByte,by have h := k.property; change k.val.length = 32 at h; simpa only [List.length_map] using h⟩

def account (e : Entry) (i : Nat) : RSL.AccountInfo :=
 let r := (e.records (e.handles i).1).owned
 ⟨key r.key,key r.owner,r.is_signer,r.is_writable,r.executable,(e.handles i).1⟩

def state (e : Entry) (next : Nat) : RSL.SdkState :=
 ⟨fun i => ⟨nativeBytes (e.buffers i),[],none⟩,next⟩

def sdkAccount (e : Entry) (i : Nat) : NLF_SdkModel.Account :=
 let r := e.records (e.handles i).1
 ⟨(key r.owned.key).bytes,(key r.owned.owner).bytes,(e.handles i).1,(e.handles i).2,
 r.owned.is_signer,r.owned.is_writable,r.owned.executable,r.rentEpoch⟩

theorem payload (e : Entry) (n i : Nat) :
 RSL.payload (account e i) (state e n) = nativeBytes (e.buffers (e.handles i).1) := rfl

theorem counters (e : Entry) (n i : Nat) :
 ((state e n).cells i).readers = [] ∧ ((state e n).cells i).writer = none := ⟨rfl,rfl⟩

theorem fresh (e : Entry) (n : Nat) : NNE_SdkState.Fresh (state e n) := by
 intro i t h
 rcases h with h | h
 · cases h
 · cases h

theorem accounts (e : Entry) (i : Nat) :
 (sdkAccount e i).data = (account e i).cell ∧
 (sdkAccount e i).key = (account e i).key.bytes ∧
 (sdkAccount e i).owner = (account e i).owner.bytes ∧
 (sdkAccount e i).signer = (account e i).is_signer ∧
 (sdkAccount e i).writable = (account e i).is_writable ∧
 (sdkAccount e i).executable = (account e i).executable :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Actual runtime SDK buffer identity is supplied by the existing admission,
not by a post-execution equality or a new association premise. -/
theorem runtime_bytes {W : Type} (L : S2Trust.Library W (Nat → Record))
 (sdk : S2TrustedSdkBorrow L) (e : Entry) (w : W) (count : Nat)
 (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e w count) (a : Nat) :
 payloadBytes S2W_ReturnedCheckpoint.encode
  (L.cellPayload w (L.accountData w a))
  (L.cellPayload w (L.accountData w a)).descriptor.length =
 MultiproofConeCanonical.bytesOf (e.buffers (account e a).cell).val := by
 exact S2W_D189Entry.native_buffer e L sdk w admission.related admission.entry.valid a

#print axioms payload
#print axioms counters
#print axioms fresh
#print axioms accounts
#print axioms runtime_bytes
end NNE_Entry
end
