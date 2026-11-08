import NMX_R9_ArgsNative241
import NMX_R6_NativeLeft242
set_option autoImplicit false
noncomputable section
namespace NMX_R9_Args241
open Aeneas Aeneas.Std Result AdapterRw

def to242 (a : RSL.TX2_241.Args) : RSL.TX2_242.Args :=
 ⟨a.program_id,a.accounts,a.data,a.current_slot⟩
def from242 (a : RSL.TX2_242.Args) : RSL.TX2_241.Args :=
 ⟨a.verifier_program,a.accounts,a.instruction_data,a.current_slot⟩
def Bounds (a : RSL.TX2_241.Args) := NMX_R6_Args242.Bounds (to242 a)
def reify (a : RSL.TX2_241.Args) (h : Bounds a) := NMX_R6_Args242.reify (to242 a) h

theorem image (n : NMX_R6_Args242.Native) :
 NMX_R9_ArgsNative241.args n.program n.accounts n.data n.slot =
 from242 (NMX_R5_Native242.args n.program n.accounts n.data n.slot) := rfl

theorem roundtrip (a : RSL.TX2_241.Args) (h : Bounds a) :
 NMX_R9_ArgsNative241.args (reify a h).program (reify a h).accounts (reify a h).data (reify a h).slot = a := by
 rw [image]
 unfold reify
 rw [NMX_R6_Args242.roundtrip]
 rfl

theorem native (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Bounds (NMX_R9_ArgsNative241.args p accounts data slot) := NMX_R6_Args242.native p accounts data slot

theorem program (p : solana_pubkey.Pubkey) (a : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError)
 (h : Bounds (NMX_R9_ArgsNative241.args p a d s)) :
 (reify (NMX_R9_ArgsNative241.args p a d s) h).program = p := NMX_R6_NativeLeft242.program p a d s h

theorem accounts (p : solana_pubkey.Pubkey) (a : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError)
 (h : Bounds (NMX_R9_ArgsNative241.args p a d s)) :
 (reify (NMX_R9_ArgsNative241.args p a d s) h).accounts = a := NMX_R6_NativeLeft242.accounts p a d s h

theorem data (p : solana_pubkey.Pubkey) (a : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError)
 (h : Bounds (NMX_R9_ArgsNative241.args p a d s)) :
 (reify (NMX_R9_ArgsNative241.args p a d s) h).data = d := NMX_R6_NativeLeft242.data p a d s h

theorem slot (p : solana_pubkey.Pubkey) (a : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError)
 (h : Bounds (NMX_R9_ArgsNative241.args p a d s)) :
 (reify (NMX_R9_ArgsNative241.args p a d s) h).slot = s := NMX_R6_NativeLeft242.slot p a d s h
#print axioms image
#print axioms roundtrip
#print axioms native
#print axioms program
#print axioms accounts
#print axioms data
#print axioms slot
end NMX_R9_Args241
end
