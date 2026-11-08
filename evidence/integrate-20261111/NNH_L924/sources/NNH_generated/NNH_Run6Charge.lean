import NNH_DeployedOuter
import NNH_Run6Numeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6Charge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH_Run6Host NNH_Run6Installed
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
variable {W Tx : Type}
/-- CONDITIONAL outer-envelope certificate. The SAME finite recorder event
bounds every actual failure pointwise and has the single adopted charge.
No expectation on an arbitrary World-dependent indicator is invented. -/
theorem deployed_charge_conditional
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NNH_Run5bCtx.Fixed) (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NNH_Run5bCtx.World W Tx) :
 (∀ H, max (0:Rat) (ind (Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH_Run5bHeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((S (Tx := Tx) L0 copy std).model1 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((S (Tx := Tx) L0 copy std).model2 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤ ind (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
   (eval H (NNH_Run5bRecorderFixed.fixedProgram copy fx anchor)))) ∧
 lazyMean (NNH_Run5bRecorderFixed.fixedProgram copy fx anchor) emptyTable
  (fun v => AspisV8R19.CausalFirstHitUnionBound.indicator
   (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965) v))
 ≤ F3T_Numeric.total (fx.Q0+fx.Q1) ∧
 (∀ H, let c := ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H
  F3T_RuntimeBound.failureModel (NNH_Run5bHost.runtime L0 copy c
   ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c)) ≤
  F3T_Numeric.total (fx.Q0+fx.Q1)) := by
 classical
 have each : ∀ H, (0:Rat) ≤ 0 + ind ((X (Tx := Tx) L0 copy std).ERec fx H) := by
  intro H
  rw [ind_def]
  split <;> norm_num
 have outer := NNH_DeployedOuter L0 borrow copy std
  allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx queries
  (fun _ => 0) (fun _ => 0) (fun _ => Rat.le_refl 0) each
 refine ⟨?_,(NNH_Run5bHostCharge.bound copy fx anchor).trans (NNH_Run6Numeric.charge_le_total _),?_⟩
 · intro H
   have h := outer wOf H
   have same : (X (Tx := Tx) L0 copy std).ERec fx H ↔
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
     (eval H (NNH_Run5bRecorderFixed.fixedProgram copy fx anchor)) :=
    NNH_Run5bFullSpace.same_event L0 copy std fx wOf H anchor
   simp only [Rat.zero_add,same] at h
   exact h
 · intro H
   exact NNH_Run6Numeric.host_bound L0 borrow copy std fx (wOf H) H queries
#print axioms deployed_charge_conditional
end AspisR1.NNH_Run6Charge
end
