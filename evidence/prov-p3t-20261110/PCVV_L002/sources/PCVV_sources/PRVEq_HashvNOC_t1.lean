import Aeneas
import NNH_HostCtx
import NOC_Run5bHost
import DGP_HostDigest
import PRVEq_AdapterStage2DeployedNOC_o1
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1
set_option autoImplicit false
noncomputable section
namespace PCVV_Hashv

/-- Item 3: LIB_Env.hashv (envOf c) is pointwise NOC_HostCtx.hashv c. This is not a restatement by rfl: it is
DGP_HostDigest.op43_value (key_digest and flatten_parts), applied at the context's own sha256/pda/clock/reservation,
because envOf c unfolds to DGP_HostDigest.envInst of those fields. -/
theorem hashv_ident {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) (parts : Slice (Slice Std.U8)) :
    LIB_Env.hashv (AspisR1.NOC_HostCtx.envOf c) parts = AspisR1.NOC_HostCtx.hashv c parts :=
  DGP_HostDigest.op43_value c.sha256 c.fixed.pda c.fixed.clock c.fixed.reservation parts

theorem hashv_ident_fun {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) :
    LIB_Env.hashv (AspisR1.NOC_HostCtx.envOf c) = AspisR1.NOC_HostCtx.hashv c :=
  funext (hashv_ident c)

/-- Seed-generic stage2 model at the headline hash: hashv := NOC_HostCtx.hashv c. -/
theorem noc_model2_hashv {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned
        (PCVP_S2.xOf (AspisR1.NOC_HostCtx.sdk c) (AspisR1.NOC_HostCtx.hashv c)) =
      AspisR1.NOC_HostCtx.model2 c :=
  PCVP_S2.generic_stage2_owned _ _ rfl (funext fun _ => funext fun parts => hashv_ident c parts)

theorem noc_validate_asq8_hashv {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.validate_asq8
        (PCVP_S2.xOf (AspisR1.NOC_HostCtx.sdk c) (AspisR1.NOC_HostCtx.hashv c)) =
      AdapterRw.r1_pool_adapter.owned.validate_asq8 (AspisR1.NOC_HostCtx.sdk c) :=
  PCVP_S2.generic_validate_asq8 _ _ rfl (funext fun _ => funext fun parts => hashv_ident c parts)

#print axioms hashv_ident
#print axioms hashv_ident_fun
#print axioms noc_model2_hashv
#print axioms noc_validate_asq8_hashv
end PCVV_Hashv
