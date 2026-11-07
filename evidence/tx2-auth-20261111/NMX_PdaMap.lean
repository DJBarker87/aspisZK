import NMX_Question
set_option autoImplicit false
noncomputable section
namespace NMX_PdaMap
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_ResultSteps

theorem try_bind {A B : Type} (r : Result A)
 (next : A → Result (core.result.Result B PE)) (tail : B → Final) :
 tryThen (r >>= next) tail = (r >>= fun a => tryThen (next a) tail) := by
 cases r <;> rfl

theorem try_ok {A : Type} (reply : core.result.Result A PE) (next : A → Final) :
 tryThen (ok reply) next = match reply with
 | .Ok a => next a
 | .Err e => ok (.Err e) := rfl

abbrev Raw := core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError

def mapped (r : Raw) : core.result.Result solana_pubkey.Pubkey PE :=
 match r with | .Ok key => .Ok key | .Err _ => .Err .InvalidAccountData

theorem master (r : Raw) :
 core.result.Result.map_err
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r () =
 ok (mapped r) := by cases r <;> rfl

theorem checkpoint (r : Raw) :
 core.result.Result.map_err
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r () =
 ok (mapped r) := by cases r <;> rfl

theorem lane (r : Raw) :
 core.result.Result.map_err
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r () =
 ok (mapped r) := by cases r <;> rfl
#print axioms try_bind
#print axioms try_ok
#print axioms master
#print axioms checkpoint
#print axioms lane
end NMX_PdaMap
end
