import NMX_Carrier
import NMX_RowSpec_233
set_option autoImplicit false
namespace NMX_CallArguments
open Aeneas Aeneas.Std AdapterRw NMX_Carrier
/-- Complete original input tuple; no index/value endpoint is a parameter. -/
def auth (a : NMX_RowSpec_233.Args) : RSL.TX2_233.Args :=
 ⟨key a.program,a.accounts.val.map account,key a.pool,byte a.lane,long a.slot⟩

def registry (verifier pool : solana_pubkey.Pubkey)
 (masterAccount : r1_pool_adapter.owned.OwnedAccount) (master : NMX_OwnedPackets.Master)
 (registry entry : r1_pool_adapter.owned.OwnedAccount) (slot : U64) : RSL.TX2_234.Args :=
 ⟨key verifier,key pool,account masterAccount,NMX_Carrier.master master,
  account registry,account entry,long slot⟩

theorem count (a : NMX_RowSpec_233.Args) :
 (auth a).accounts.length = a.accounts.val.length := List.length_map

theorem seven (a : NMX_RowSpec_233.Args)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount)
 (shape : a.accounts.val = [p,m,c,l,r,e,v]) :
 (auth a).accounts = [account p,account m,account c,account l,account r,account e,account v] := by
 simp only [auth,shape,List.map_cons,List.map_nil]

theorem registry_same (verifier pool : solana_pubkey.Pubkey)
 (ma : r1_pool_adapter.owned.OwnedAccount) (m : NMX_OwnedPackets.Master)
 (r e : r1_pool_adapter.owned.OwnedAccount) (slot : U64) :
 registry verifier pool ma m r e slot =
 ⟨key verifier,key pool,account ma,master m,account r,account e,long slot⟩ := rfl

theorem lane_same (input : Slice U8) : NMX_Carrier.bytes input = input.val.map byte := rfl
#print axioms count
#print axioms seven
#print axioms registry_same
#print axioms lane_same
end NMX_CallArguments
