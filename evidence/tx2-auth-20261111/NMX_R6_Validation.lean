import NMX_R6_NativeLive242
import NMX_R6_Args242
import NMX_R6_Port242
set_option autoImplicit false
noncomputable section
namespace NMX_R6_Validation
open Aeneas Aeneas.Std AdapterRw RSL NMS_R2N_Interpreted
attribute [local instance] Classical.propDecidable

/-- On represented inputs this is a selection from the emitted native body,
with every fixed child and std interpretation installed. Non-representable
mathematical Args use the explicit same-order source-control port. The latter
retains the library's oversized-buffer panic; Domain remains True. -/
def validate (choices : NMX_R4_Authentication.Choices) (a : TX2_242.Args) (env : Env) :
 Obs (Except ProgramError (TX2_242.Validated LIBB_PoolLib.library)) :=
 if represented : NMX_R6_Args242.Bounds a then
  let n := NMX_R6_Args242.reify a represented
  mapObs (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
   (NMX_R6_NativeLive242.observation choices n.program n.accounts n.data n.slot env)
 else NMX_R6_Port242.validate choices a env

/-- Complete242 packet, with no child, library, Ops, successful-allocation or
representation premise. Only the std choices of the already-complete233
implementation are quantified. Native source selection never consults Ref. -/
theorem root (choices : NMX_R4_Authentication.Choices) :
 TX2_242.RowSpec_242 LIBB_PoolLib.library LIBB_PoolLib.deployed (validate choices) := by
 intro a env _
 unfold validate
 split
 · rename_i h
   let n := NMX_R6_Args242.reify a h
   have run := NMX_R6_NativeLive242.source_member choices n.program n.accounts n.data n.slot env
   have packet := NMX_R5_Native242.full choices n.program n.accounts n.data n.slot env _ run
   rw [NMX_R6_Args242.roundtrip a h] at packet
   exact packet
 · exact NMX_R4_NMS242Instantiation.fold choices a env _ (NMX_R6_Port242.replay_member choices a env)

/-- Every actual native input takes the source branch. No source-size
hypothesis is imposed on a caller. -/
theorem native_branch (choices : NMX_R4_Authentication.Choices)
 (program : AdapterRw.solana_pubkey.Pubkey)
 (accounts : Aeneas.Std.Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
 (data : Aeneas.Std.Slice Aeneas.Std.U8)
 (slot : core.result.Result Aeneas.Std.U64 AdapterRw.solana_program_error.ProgramError)
 (env : Env) :
 validate choices (NMX_R5_Native242.args program accounts data slot) env =
 let a := NMX_R5_Native242.args program accounts data slot
 let n := NMX_R6_Args242.reify a (NMX_R6_Args242.native program accounts data slot)
 mapObs (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (NMX_R6_NativeLive242.observation choices n.program n.accounts n.data n.slot env) := by
 unfold validate
 rw [dif_pos (NMX_R6_Args242.native program accounts data slot)]

#print axioms root
#print axioms native_branch
end NMX_R6_Validation
end
