import NMX_R6_AccountLeft
set_option autoImplicit false
noncomputable section
namespace NMX_R6_NativeLeft242
open Aeneas Aeneas.Std Result AdapterRw
open NMX_R6_Args242

theorem list : ∀ (xs : List r1_pool_adapter.owned.OwnedAccount)
 (h : ∀ a ∈ xs.map NMX_R2_Carrier.account, NMX_R2_AccountReify.Bounds a),
 NMX_R2_AccountListReify.list (xs.map NMX_R2_Carrier.account) h = xs
 | [],h => rfl
 | a::rest,h => by
   simp only [List.map_cons,NMX_R2_AccountListReify.list,NMX_R6_AccountLeft.account]
   exact congrArg (List.cons a) (list rest _)

theorem program (p : solana_pubkey.Pubkey) (as_ : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError)
 (h : Bounds (NMX_R5_Native242.args p as_ d s)) :
 (reify (NMX_R5_Native242.args p as_ d s) h).program = p := by
 change NMX_R2_InverseBytes.fromKey (NMS_R2N_RSLScalars.b32 p) = p
 rw [NMX_R4_NMSCarrier.key]
 exact NMX_R2_InverseBytes.array_roundtrip p

theorem accounts (p : solana_pubkey.Pubkey) (as_ : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError)
 (h : Bounds (NMX_R5_Native242.args p as_ d s)) :
 (reify (NMX_R5_Native242.args p as_ d s) h).accounts = as_ := by
 apply Subtype.ext
 change NMX_R2_AccountListReify.list (as_.val.map NMS_R2N_RSLPoolCarriers.account) _ = as_.val
 simp only [NMX_R4_NMSCarrier.accounts]
 exact list as_.val _

theorem data (p : solana_pubkey.Pubkey) (as_ : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError)
 (h : Bounds (NMX_R5_Native242.args p as_ d s)) :
 (reify (NMX_R5_Native242.args p as_ d s) h).data = d :=
 LIBB_Bytes.from_bytes d h.2

theorem long (n : U64) : NMX_R2_ArgsReify.fromLong (NMS_R2N_RSLScalars.u64 n) = n := by
 have h := NMX_R2_ArgsReify.long_roundtrip (NMS_R2N_RSLScalars.u64 n)
 rw [LIBB_AccountCarriers.long] at h
 change NMS_R2N_RSLScalars.u64 (NMX_R2_ArgsReify.fromLong (NMS_R2N_RSLScalars.u64 n)) =
  NMS_R2N_RSLScalars.u64 n at h
 have same := congrArg NMS_R2N_RSLScalars.raw64 h
 simpa only [NMS_R2N_RSLScalars.u64_left] using same

theorem slot (p : solana_pubkey.Pubkey) (as_ : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError)
 (h : Bounds (NMX_R5_Native242.args p as_ d s)) :
 (reify (NMX_R5_Native242.args p as_ d s) h).slot = s := by
 change NMX_R6_Args242.slot (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 s) = s
 cases s with
 | Ok n => exact congrArg core.result.Result.Ok (long n)
 | Err e => exact congrArg core.result.Result.Err (NMS_R2N_RSLError.left e)

#print axioms list
#print axioms program
#print axioms accounts
#print axioms data
#print axioms long
#print axioms slot
end NMX_R6_NativeLeft242
end
