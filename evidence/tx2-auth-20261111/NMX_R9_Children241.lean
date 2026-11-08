import NMX_R8_Children241
set_option autoImplicit false
noncomputable section
namespace NMX_R9_Children241
open Aeneas Aeneas.Std Result AdapterRw

/-- Every observation of the complete emitted242 meaning at the SAME tuple.
No single source observation is selected at this native call site. -/
def validate (choices : NMX_R4_Authentication.Choices) :=
 NMS_R2N_Native242Children.meaning false (NMX_R4_NMS233.typed choices)

def grouped (choices : NMX_R4_Authentication.Choices) : NMX_R8_Code241.Effects RSL.Spec :=
 {NMX_R8_Children241.grouped choices with validate := validate choices}

def original (choices : NMX_R4_Authentication.Choices) : NMS_Effect241.Effects RSL.Spec :=
 {NMX_R8_Children241.original choices with validate := validate choices}

/-- Full242 law, not just the graph chosen for its function-shaped row packet. -/
theorem validate_full (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (a : Slice r1_pool_adapter.owned.OwnedAccount)
 (d : Slice U8) (s : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (validate choices p a d s)
  (RSL.TX2_242.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed (NMX_R5_Native242.args p a d s)) :=
 NMX_R5_Native242.full choices p a d s
#print axioms validate_full
end NMX_R9_Children241
end
