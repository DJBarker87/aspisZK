import NNH_HostExec
import NNH_MAccountCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_PhysicalCarriers
open Aeneas Aeneas.Std S2W_ReturnedCheckpoint

theorem byte (b : U8) : nativeByte b = NND_Carrier.byte b := by
 apply UInt8.toBitVec_inj.mp
 change BitVec.ofNat 8 b.bv.toNat = b.bv
 simp

theorem bytes (bs : Slice U8) : nativeBytes bs = NND_Carrier.bytes bs := by
 unfold nativeBytes NND_Carrier.bytes
 apply List.map_congr_left
 intro b _
 exact byte b

theorem key (k : _root_.AdapterRw.solana_pubkey.Pubkey) : NNE_Entry.key k = NND_Carrier.key k := by
 unfold NNE_Entry.key NND_Carrier.key
 congr 1
 apply List.map_congr_left
 intro b _
 exact byte b

theorem owned (a : S2W_D189Entry.Owned) :
 NNE_Snapshot.owned NND_Carrier.error a = NNH_ModelCarrier.account a := by
 unfold NNE_Snapshot.owned NNH_ModelCarrier.account
 rw [key,key]
 cases a.length <;> cases a.bytes <;> simp only [NND_Carrier.reply,bytes]

theorem accounts (xs : S2W_ExtractionBoundary.Accounts) :
 xs.val.map (NNE_Snapshot.owned NND_Carrier.error) = NNH_ModelCarrier.accounts xs := by
 unfold NNH_ModelCarrier.accounts
 apply List.map_congr_left
 intro a _
 exact owned a
#print axioms byte
#print axioms bytes
#print axioms key
#print axioms owned
#print axioms accounts
end AspisR1.NNH_PhysicalCarriers
end
