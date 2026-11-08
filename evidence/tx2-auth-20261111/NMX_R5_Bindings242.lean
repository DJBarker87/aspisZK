import NMX_R4_NMS233
import NMS_R2Tail242
import NMS_R2AfterAuth242
import LIBB_PoolScan
import LIBB_PoolReconstruct
set_option autoImplicit false
noncomputable section
namespace NMX_R5_Bindings242
open Aeneas Aeneas.Std AdapterRw

theorem typed_parent (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_R2Refine.Refines
  (NMS_R2N_Native242Children.meaning false (NMX_R4_NMS233.typed choices) program accounts data slot)
  (NMS_R2Parameterized242.Ref false LIBB_PoolLib.library LIBB_PoolLib.deployed program accounts data slot) :=
 NMS_R2Parameterized242.fold false _ _ _ (NMX_R4_NMS233.packet choices) program accounts data slot

/-- Full source scanner/reconstruction laws, including the source Box aborts,
are installed from the supplied LIBB fields at SAME byte/request/auth inputs. -/
theorem tail (q : NMS_R2Tail242.Request) (auth : NMS_R2Tail242.Auth)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 NMS_R2N_Interpreted.Simulates
  (NMS_R2N_RSLError.reply (NMS_R2Tail242.validatedValue LIBB_PoolLib.library id))
  (NMS_R2Tail242.raw q auth a)
  (RSL.RS.bind (NMS_R2N_RSLPoolCarriers.account a).data fun data =>
   RSL.RS.bind (LIBB_PoolLib.library.scanProof data) fun scanned =>
   RSL.RS.bind (LIBB_PoolLib.library.reconstruct q
    (NMS_R2N_RSLPoolCarriers.authenticated auth) scanned.1) fun st =>
   RSL.RS.pure ⟨st,scanned.2⟩) := by
 apply NMS_R2Tail242.transport LIBB_PoolLib.library id id id
 · intro data
   exact LIBB_PoolScan.native_copy data
 · intro request authenticated candidate
   rw [LIBB_AuthCarrier.exact_carrier]
   exact LIBB_PoolReconstruct.native_copy request authenticated candidate
#print axioms typed_parent
#print axioms tail
end NMX_R5_Bindings242
end
