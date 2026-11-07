import NNH_Libraries
import NNC_ObservedLaw
set_option autoImplicit false
noncomputable section
namespace NNH_064Parser
open Aeneas Aeneas.Std AspisR1 VTop_Stages NLW_Full064
/-- This endpoint is never entered on a parser-stop branch. It supplies no
common invocation, child result or suffix event to any native proof below. -/
def unreachable (env : RSL.Env) : transport.Variant →
 NLT_CompleteRoot.End (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () :=
 fun _ => .resolved .div []

/-- Exact emitted-parser interpretation on all three non-common arms. The
common-entered case remains a separate integration obligation. -/
theorem native {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient)
 (stopped : ∀ v, NLE_ParseInstall.parse proof≠.ok (.Ok v)) :
 NNC_ObservedWeak.Observed (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩
  (LIBB_Tx2EnvTrace.observation env pub proof ck) := by
 let frame : NLW_Full064.Frame Ambient Unit :=
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩
 have parser : NMN_064.ParserNative proof (NLE_ParseInstall.parse proof) :=
  LIBB_Tx2EnvCode.parser proof
 have actual := NMN_064.Native.observed (LIBB_PartitionEnv.H env) frame
  (NLE_ParseInstall.parse proof) (unreachable env) parser
  (fun v same => False.elim (stopped v same))
 unfold NNC_ObservedWeak.Observed
 refine ⟨(NMN_OracleFold.run (LIBB_PartitionEnv.H env) frame
   (NLE_ParseInstall.parse proof) (unreachable env)).1,
  (NMN_OracleFold.run (LIBB_PartitionEnv.H env) frame
   (NLE_ParseInstall.parse proof) (unreachable env)).2,[],actual,?_,?_⟩
 · cases parsed : NLE_ParseInstall.parse proof with
   | fail e => rfl
   | div => rfl
   | ok r => cases r with
     | Err e => rfl
     | Ok v => exact False.elim (stopped v parsed)
 · cases parsed : NLE_ParseInstall.parse proof with
   | fail e =>
    unfold LIBB_Tx2EnvTrace.observation LIBB_Tx2EnvTrace.events LIBB_Tx2EnvCode.code
    rw [parsed]
    rfl
   | div =>
    unfold LIBB_Tx2EnvTrace.observation LIBB_Tx2EnvTrace.events LIBB_Tx2EnvCode.code
    rw [parsed]
    rfl
   | ok r => cases r with
     | Err e =>
      unfold LIBB_Tx2EnvTrace.observation LIBB_Tx2EnvTrace.events LIBB_Tx2EnvCode.code
      rw [parsed]
      rfl
     | Ok v => exact False.elim (stopped v parsed)

/-- The unchanged NNC weak law contains exactly this actual parser endpoint
at the SAME byte carriers. No Root0 or domain clause is needed on these arms. -/
theorem weak {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient)
 (stopped : ∀ v, NLE_ParseInstall.parse proof≠.ok (.Ok v)) :
 NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
  (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env
  (LIBB_Tx2EnvTrace.observation env pub proof ck) :=
 ⟨pub,proof,ck,rfl,rfl,rfl,native env pub proof ck world stopped⟩

#print axioms native
#print axioms weak
end NNH_064Parser
