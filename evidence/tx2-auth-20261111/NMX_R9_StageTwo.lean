import NMX_R9_Live241
import NMX_R9_Args241
import NMX_R7_PortLaw241
set_option autoImplicit false
noncomputable section
namespace NMX_R9_StageTwo
open Aeneas Aeneas.Std Result AdapterRw RSL NMS_R2N_Interpreted
attribute [local instance] Classical.propDecidable
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed
abbrev V := LIBB_V2Star.library

def stage2 (choices : NMX_R4_Authentication.Choices) (a : TX2_241.Args) (env : Env) :
 Obs (Except ProgramError Unit) :=
 if represented : NMX_R9_Args241.Bounds a then
  let n := NMX_R9_Args241.reify a represented
  mapObs (NMS_R2N_RSLError.reply id) (NMX_R9_Live241.observation choices n.program n.accounts n.data n.slot env)
 else NMX_R7_Port241.stage2 choices a env

/-- Complete canonical241 candidate. Only original D1/D2 remain; every native
244 outcome and full064 observation is retained by Native241.full. No Ops,
child/law/library/success/representation premise is retained. -/
theorem root (choices : NMX_R4_Authentication.Choices) : TX2_241.RowSpec_241 L D V (stage2 choices) := by
 intro a env domain
 unfold stage2
 split
 · rename_i h
   let n := NMX_R9_Args241.reify a h
   have image := NMX_R9_Args241.roundtrip a h
   have sourceDomain : TX2_241.Domain V (NMX_R9_ArgsNative241.args n.program n.accounts n.data n.slot) := by
    rw [image]
    exact domain
   have run := NMX_R9_Live241.source_member choices n.program n.accounts n.data n.slot env
   have law := NMX_R9_Native241.full choices n.program n.accounts n.data n.slot sourceDomain env _ run
   rw [image] at law
   exact law
 · exact NMX_R7_PortLaw241.canonical choices a env domain

theorem observed (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) (env : Env) :
 stage2 choices (NMX_R9_ArgsNative241.args p accounts data slot) env =
 mapObs (NMS_R2N_RSLError.reply id) (NMX_R9_Live241.observation choices p accounts data slot env) := by
 unfold stage2
 rw [dif_pos (NMX_R9_Args241.native p accounts data slot)]
 simp only [NMX_R9_Args241.program,NMX_R9_Args241.accounts,NMX_R9_Args241.data,NMX_R9_Args241.slot]

/-- Complete source observation at the EXACT original typed tuple; errors,
independent stops and every event prefix are included. -/
theorem source (choices : NMX_R4_Authentication.Choices)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) (env : Env) :
 ∃ o, NMX_R9_Native241.meaning choices p accounts data slot env o ∧
 stage2 choices (NMX_R9_ArgsNative241.args p accounts data slot) env = mapObs (NMS_R2N_RSLError.reply id) o :=
 ⟨_,NMX_R9_Live241.source_member choices p accounts data slot env,observed choices p accounts data slot env⟩
#print axioms root
#print axioms observed
#print axioms source
end NMX_R9_StageTwo
end
