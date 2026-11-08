import NMX_R5_Native242
import NMX_R2_NativeBounds
import LIBB_Bytes
set_option autoImplicit false
noncomputable section
namespace NMX_R6_Args242
open Aeneas Aeneas.Std Result AdapterRw

def base (a : RSL.TX2_242.Args) : RSL.TX2_233.Args :=
 ⟨a.verifier_program,a.accounts,RSL.zero32,0,0⟩

def Bounds (a : RSL.TX2_242.Args) : Prop :=
 NMX_R2_ArgsReify.Bounds (base a) ∧ a.instruction_data.length ≤ Usize.max

structure Native where
 program : solana_pubkey.Pubkey
 accounts : Slice r1_pool_adapter.owned.OwnedAccount
 data : Slice U8
 slot : core.result.Result U64 solana_program_error.ProgramError

def slot (r : Except RSL.ProgramError UInt64) : core.result.Result U64 solana_program_error.ProgramError :=
 match r with
 | .ok n => .Ok (NMX_R2_ArgsReify.fromLong n)
 | .error e => .Err (NMS_R2N_RSLError.raw e)

def reify (a : RSL.TX2_242.Args) (h : Bounds a) : Native :=
 let n := NMX_R2_ArgsReify.reify (base a) h.1
 ⟨n.program,n.accounts,LIBB_Bytes.fromBytes a.instruction_data h.2,slot a.current_slot⟩

theorem slot_roundtrip (r : Except RSL.ProgramError UInt64) :
 NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 (slot r) = r := by
 cases r with
 | ok n => exact congrArg Except.ok (by
    change NND_Carrier.slot (NMX_R2_ArgsReify.fromLong n) = n
    rw [←LIBB_AccountCarriers.long]
    exact NMX_R2_ArgsReify.long_roundtrip n)
 | error e => exact congrArg Except.error (NMS_R2N_RSLError.right e)

theorem ext (a b : RSL.TX2_242.Args)
 (hp : a.verifier_program = b.verifier_program) (ha : a.accounts = b.accounts)
 (hd : a.instruction_data = b.instruction_data) (hs : a.current_slot = b.current_slot) : a = b := by
 cases a
 cases b
 simp_all

theorem roundtrip (a : RSL.TX2_242.Args) (h : Bounds a) :
 NMX_R5_Native242.args (reify a h).program (reify a h).accounts (reify a h).data (reify a h).slot = a := by
 have b := NMX_R2_ArgsReify.roundtrip (base a) h.1
 have program := congrArg RSL.TX2_233.Args.verifier_program b
 have accounts := congrArg RSL.TX2_233.Args.accounts b
 simp only [NMX_R2_CallArguments.auth,base] at program accounts
 apply ext
 · simpa only [base,NMX_R5_Native242.args,reify,NMX_R4_NMSCarrier.key] using program
 · simpa only [base,NMX_R5_Native242.args,reify,NMS_R2N_RSLPoolCarriers.accounts,
    NMX_R4_NMSCarrier.accounts] using accounts
 · change LIBB_Bytes.bytes (LIBB_Bytes.fromBytes a.instruction_data h.2) = _
   exact LIBB_Bytes.bytes_from _ _
 · exact slot_roundtrip a.current_slot

/-- Native inputs always take the represented branch. This is a carrier fact,
not a premise of the canonical Domain=True theorem. -/
theorem native (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Bounds (NMX_R5_Native242.args program accounts data slot) := by
 constructor
 · constructor
   · simpa only [base,NMX_R5_Native242.args,NMS_R2N_RSLPoolCarriers.accounts,List.length_map] using accounts.property
   · intro a ha
     change a ∈ accounts.val.map NMS_R2N_RSLPoolCarriers.account at ha
     obtain ⟨raw,_,same⟩ := List.mem_map.mp ha
     subst a
     rw [NMX_R4_NMSCarrier.account]
     exact NMX_R2_NativeBounds.account raw
 · change (NMS_R2N_RSLScalars.bytes data).length ≤ Usize.max
   rw [NMS_R2N_RSLScalars.bytes_length]
   exact data.property

#print axioms ext
#print axioms slot_roundtrip
#print axioms roundtrip
#print axioms native
end NMX_R6_Args242
end
