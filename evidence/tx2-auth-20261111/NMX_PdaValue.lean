import NMX_PdaMap
set_option autoImplicit false
noncomputable section
namespace NMX_PdaValue
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_ResultSteps

theorem raw (reply : NMX_PdaMap.Raw) (next : solana_pubkey.Pubkey → Final) :
 tryThen (match reply with
 | .Ok key => ok (.Ok key)
 | .Err _ => ok (.Err .InvalidAccountData)) next =
 match reply with
 | .Ok key => next key
 | .Err _ => ok (.Err .InvalidAccountData) := by
 cases reply <;> rfl

theorem mapped (reply : NMX_PdaMap.Raw) (next : solana_pubkey.Pubkey → Final) :
 (match NMX_PdaMap.mapped reply with
 | .Ok key => next key
 | .Err error => ok (.Err error)) =
 match reply with
 | .Ok key => next key
 | .Err _ => ok (.Err .InvalidAccountData) := by
 cases reply <;> rfl
#print axioms raw
#print axioms mapped
end NMX_PdaValue
end
