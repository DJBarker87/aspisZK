import NMB_MetadataAdmission
import NLM_RuntimeInput
set_option autoImplicit false
noncomputable section
namespace NMB_Input
open Aeneas Aeneas.Std Result AspisR1
abbrev Owned := AdapterRw.r1_pool_adapter.owned.OwnedAccount
/-- Original descriptors are indexed by account occurrence; actual byte and
lamport allocations remain indexed by their runtime cells. -/
structure Input where
 handles : Nat → Nat × Nat
 descriptors : Nat → Owned
 buffers : Nat → Slice U8
 money : Nat → Nat
 rentEpoch : Nat → Nat
 base : Nat → Nat
 provenance : Nat → Nat

def Input.records (x : Input) (a : Nat) : NLF_SdkModel.Account :=
 let d := x.descriptors a
 ⟨S2W_ReturnedCheckpoint.nativeBytes d.key.to_slice,
  S2W_ReturnedCheckpoint.nativeBytes d.owner.to_slice,
  (x.handles a).1,(x.handles a).2,d.is_signer,d.is_writable,d.executable,x.rentEpoch a⟩
def Input.sdk (x : Input) : NLF_SdkModel.State :=
 ⟨x.records,fun i => ⟨⟨S2W_ReturnedCheckpoint.nativeBytes (x.buffers i),x.money i⟩,[],none⟩⟩
def Input.snapshot (x : Input) (a lo hi : Nat) : Owned :=
 let bytes := x.buffers (x.handles a).1
 {(x.descriptors a) with
   length := .Ok (Slice.len bytes)
   bytes := if bytes.val.length=lo ∨ bytes.val.length=hi then .Ok bytes
     else .Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData}
def ofEntry (e : S2W_D189Entry.Entry) : Input :=
 ⟨e.handles,fun a => (e.records (e.handles a).1).owned,e.buffers,
  fun i => (e.records i).lamports,fun a => (e.records (e.handles a).1).rentEpoch,
  e.base,e.provenance⟩
theorem entry_snapshot (e : S2W_D189Entry.Entry) (a lo hi : Nat) :
 (ofEntry e).snapshot a lo hi = e.snapshot a lo hi := rfl
/-- The old cell-indexed interpretation is one specialization, not a premise
that different occurrences sharing a data handle have equal privileges. -/
theorem entry_sdk (e : S2W_D189Entry.Entry) :
 (ofEntry e).sdk = (NLM_RuntimeInput.initial e).state := by
 change NLF_SdkModel.State.mk _ _ = NLF_SdkModel.State.mk _ _
 congr 1
 funext i
 congr 2
 exact (NLM_RuntimeInput.payload_bytes e i).symm
#print Input
#print axioms entry_snapshot
#print axioms entry_sdk
end NMB_Input
