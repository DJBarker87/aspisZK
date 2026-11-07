import NND_DecoderSlots
import LIBB_PolicyValue
import LIBB_Bytes
import RSL_TX2_234
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryOps
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
attribute [local instance] Classical.propDecidable
/-- Pure value interpretation of the runtime PDA reply after the source's
map_err boundary. Outer runtime-stop transport is a separate obligation. -/
def pda (env : RSL.Env) (parts : Slice (Slice U8)) (program : solana_pubkey.Pubkey) :
 Result (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) :=
 ok (match env.pda (parts.val.map bytes) (key program) with
  | some k => .Ok (unkey k)
  | none => .Err .InvalidSeeds)

/-- All selected helpers are concrete. This local dictionary is NOT yet the
headline's missing instance: runtime representation and native217 remain OPEN. -/
def install (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) : Ops :=
 {NND_DecoderSlots.install base with
  op13 := ok 1#u8
  op14 := ok 2#u8
  op15 := NHY_PolicyModel.policy
  op18 := ok 1#u8
  op35 := fun e => ok e
  op36 := fun a b => ok (decide (a = b))
  op37 := fun k => ok k
  op38 := pda env
  op39 := fun k => ok k
  op40 := fun k => ok (Array.to_slice k)
  op41 := ok (unkey RSL.LOADER_ID)
  op45 := ok (unkey D.pool)
  op46 := ok (unkey D.registry)}

theorem policy (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) :
 (install base D env).op15 = NHY_PolicyModel.policy := rfl

theorem pda_selected (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) :
 (install base D env).op38 = pda env := rfl

#print axioms policy
#print axioms pda_selected
end NMX_R3_RegistryOps
end
