/-
TX1:330  programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction (TX1 occurrence)
Same frozen function and signature as TX2:213 (lib.rs:56).  RowSpec_330 is
RowSpec_213 with the stage1 child instantiated by TX1:344's packet; the two
rows carry one identical full statement (every instruction byte string is
covered: non-admitted data is rejected before any account is touched).
Route: guard-holding entry, ReviewedTranscription plus (bj)/(bl) cuts.
Own-input domain: TX2_213.Domain at S1 = TX1_344.asStage1: (E1) the Root0
clause on the ASQ8 route; (E2) True on the stage1 route.
-/
import RSL_TX1_333
import RSL_TX2_213
set_option autoImplicit false

namespace RSL.TX1_330
open TX2_241 (V2Lib)
open TX1_345 (S1Lib)

def RowSpec_330 (L : PoolLib) (D : DeployedIds) (V2 : V2Lib) (V : VLib) (P : PreparedNew V)
    (C : S1Lib V)
    (process_r1_cost_probe_instruction :
      TX2_213.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)) : Prop :=
  TX2_213.RowSpec_213 L D V2 (TX1_344.asStage1 V P C) process_r1_cost_probe_instruction

def RowSpec_213_full := @RowSpec_330

theorem rejects_constAbort (L : PoolLib) (D : DeployedIds) (V2 : V2Lib) (V : VLib)
    (P : PreparedNew V) (C : S1Lib V) :
    ¬ RowSpec_330 L D V2 V P C (fun a s => constAbort (a, s)) :=
  TX2_213.rejects_constAbort L D V2 _

theorem rejects_silentErr (L : PoolLib) (D : DeployedIds) (V2 : V2Lib) (V : VLib)
    (P : PreparedNew V) (C : S1Lib V) (e : ProgramError) (f : SdkState → SdkState) :
    ¬ RowSpec_330 L D V2 V P C (TX2_240.silentErr e f) :=
  TX2_213.rejects_silentErr L D V2 _ e f

end RSL.TX1_330
