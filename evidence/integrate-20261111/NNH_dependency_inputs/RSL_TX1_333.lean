/-
TX1:333  programs/r1-cost-probe/src/r1_pool_adapter.rs::process (TX1 occurrence)
Same frozen function and signature as TX2:221 (r1_pool_adapter.rs:950).  The
row's obligation is the function's complete obligation, so RowSpec_333 is
RowSpec_221 with the stage1 child instantiated by TX1:344's packet
(`TX1_344.asStage1`).  RowSpec_221_full is the identical Prop; both rows close
together, by one root over both routes.
Route: guard-holding dispatcher, ReviewedTranscription plus (bj)/(bl) cuts.
Own-input domain: TX2_221.Domain at S1 = TX1_344.asStage1, i.e. (P1) admitted
data, (P2) TX2:240's Root0 clause on the ASQ8 route, (P3) True on the stage1
route (TX1:344 has no own-input domain).
-/
import RSL_TX1_344
set_option autoImplicit false

namespace RSL.TX1_333
open TX2_241 (V2Lib)
open TX1_345 (S1Lib)

def RowSpec_333 (L : PoolLib) (D : DeployedIds) (V2 : V2Lib) (V : VLib) (P : PreparedNew V)
    (C : S1Lib V)
    (process : TX2_221.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)) : Prop :=
  TX2_221.RowSpec_221 L D V2 (TX1_344.asStage1 V P C) process

/-- TX2:221's statement with its stage1 parameter instantiated: the same Prop. -/
def RowSpec_221_full := @RowSpec_333

/-- Rejection inherited from TX2:221 (any stage1 law). -/
theorem rejects_silentErr (L : PoolLib) (D : DeployedIds) (V2 : V2Lib) (V : VLib)
    (P : PreparedNew V) (C : S1Lib V) (e : ProgramError) (f : SdkState → SdkState) :
    ¬ RowSpec_333 L D V2 V P C (TX2_240.silentErr e f) :=
  TX2_221.rejects_silentErr L D V2 _ e f

end RSL.TX1_333
