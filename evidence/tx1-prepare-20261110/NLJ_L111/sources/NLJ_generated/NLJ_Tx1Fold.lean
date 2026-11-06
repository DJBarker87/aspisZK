import NLJ_Tx1Step
import NHZ_NativeAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Tx1
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect (Code)
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult
def fold (cfg : Configuration) : Nat → State → Code Out
 | 0,_ => liftM (fail .panic)
 | n+1,s => do
   let post ← step cfg s
   match post with | .inl out => pure out | .inr after => fold cfg n after
/-- Source cut tree indexed by the exact code. Native existence and callee
packet installation are NOT inferred by this definition. -/
def Cuts (cfg : Configuration) (i : Input) (out : Result Out) (log : SdkC_Source.Log) : Prop :=
 NHZ_DRIVER.Cuts i.hashv (fold cfg 20 ⟨i,.guard⟩) out log
/-- Complete Result/effect fold, not an admitted native row root. -/
theorem source_fold (cfg : Configuration) (i : Input) (out : Result Out)
 (log : SdkC_Source.Log) (cuts : Cuts cfg i out log) (before : SdkC_Source.Log) :
 SdkC_Source.run i.hashv (fold cfg 20 ⟨i,.guard⟩) before = (out,before++log) :=
 NHZ_DRIVER.frame cuts before
/-- Exact next SOURCE goal. This equation has not been proved and must not be
smuggled into a native row root as an endpoint/body premise. -/
def SourceEquality (cfg : Configuration) (i : Input) : Prop :=
 SdkC_Source.run i.hashv (fold cfg 20 ⟨i,.guard⟩) [] =
 SdkC_Source.run i.hashv
  (GExp_FirstCode.code cfg.base cfg.boundaries cfg.std i.hashv i.digest i.publicValue i.publicBytes i.proof i.k) []
#print axioms source_fold
#print source_fold
#print SourceEquality
end AspisR1.NLJ_Tx1
end
