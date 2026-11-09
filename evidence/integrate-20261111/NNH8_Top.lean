import NNH8_NMF
import NNH8_Rest
import NNH8_Charge
import NNH_Run6Charge
set_option autoImplicit false
noncomputable section
/-! Run 7 (G0 FINAL) assembly helpers at the corrected host S := NOC_Run5bHost.S_host.
These are the run-6 NNH_Run6Host/Physical/Top/Numeric/DeployedOuter/Charge bodies with
every host constant replaced by its corrected-host restatement. They still take a1, a2 and
rest as arguments ONLY so that this module does not import the A1/A2 closures; the
deliverables AspisR1.TAS_FinalB.deployed_splitB / deployed_charge instantiate all three
with delivered closed terms and carry no such argument. These helpers are not claims. -/
namespace AspisR1.NNH8_TopHost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Libraries
variable {W Tx : Type}
 (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
abbrev S := NOC_Run5bHost.S_host (Tx := Tx) L0 copy std
abbrev R := NNH8_Exec.recSig (Tx := Tx) L0 copy std
abbrev X := NNH8_Exec.exec (Tx := Tx) L0 copy std
abbrev RestLaw := NNH8_Rest.Delivered (Tx := Tx) L0 copy std

def split (rest : RestLaw (Tx := Tx) L0 copy std) : RSL.TFM.Split (S (Tx := Tx) L0 copy std) where
 Rest := NNH8_Split.rest L0 copy
 Outcome := NNH8_Split.outcome L0 copy
 concl_iff := NNH8_Split.conclusion_iff L0 copy
 rest := rest

theorem sig_same : NNH_G1aEnv.sig (S (Tx := Tx) L0 copy std) = S (Tx := Tx) L0 copy std := rfl

def g1a (I : RSL.TAS.Impl L V0 VL) : RSL.NNT.NNC_G1aL (S (Tx := Tx) L0 copy std) L V0 VL I :=
 NNT_G1aLaw.field (S (Tx := Tx) L0 copy std) I

def nmfB (I : RSL.TAS.Impl L V0 VL) :
 NNT_TopL.NNC_NMFPrimeB (S (Tx := Tx) L0 copy std) L D V0 VL P C I
  (g1a L0 copy std I) (R L0 copy std) := NNH8_NMF.nmfB L0 copy std I

example (I : RSL.TAS.Impl L V0 VL) : (g1a (Tx := Tx) L0 copy std I).w = V0.tx2auth := rfl
example : (X (Tx := Tx) L0 copy std).exhibited_mk = (fun _ _ _ _ _ => rfl) := rfl
#print axioms split
#print axioms sig_same
#print axioms g1a
#print axioms nmfB
end AspisR1.NNH8_TopHost
namespace AspisR1.NNH8_Physical
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH8_TopHost
open NNH_Run6Fields
variable {W Tx : Type}
/-- CONDITIONAL only. Exactly A1, A2 and Split.rest remain explicit obligations.
No row credit, condition-(4) verdict or final headline is asserted. -/
theorem deployed_splitB_of
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (I0 : Impl L V0 VL)
 (allocation217 : Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NOC_Run5bCtx.Fixed) (w : NOC_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (run : Runs (S (Tx := Tx) L0 copy std) (I I0 allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx w H)) :
 let c := ctxB (X (Tx := Tx) L0 copy std) fx w H
 (S (Tx := Tx) L0 copy std).Bound c ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∧
 NNH8_Split.rest L0 copy c ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∧
 ((NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec c
  ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∨ (X (Tx := Tx) L0 copy std).ERec fx H) := by
 exact NNT_TopL.top_splitB_physical L D V0 VL P C (I I0 allocation217 allocation234 ch alloc1 alloc2)
  (split L0 copy std rest) (NNH8_Headline.headline L0 borrow copy std)
  (NOC_Run5bHost.a0 L0 copy std)
  (nmm I0 allocation217 allocation234 ch alloc1 alloc2)
  (nmx I0 allocation217 allocation234 ch alloc1 alloc2)
  (nms I0 allocation217 allocation234 ch alloc1 alloc2)
  (nmv I0 allocation217 allocation234 ch alloc1 alloc2)
  (nmw I0 allocation217 allocation234 ch alloc1 alloc2)
  (nmt I0 allocation217 allocation234 ch alloc1 alloc2)
  (nmp I0 allocation217 allocation234 ch alloc1 alloc2)
  (nmo I0 allocation217 allocation234 ch alloc1 alloc2)
  (g1a L0 copy std _) (NNH8_Exec.recSelect L0 copy std)
  (NNH8_HeadlineB.headlineB L0 borrow copy std) (nmfB L0 copy std _)
  (NOC_Run5bHost.r0 L0 copy std) a1 a2
  (NNH8_Acceptance.a3 L0 copy std) (NNH8_Acceptance.a4 L0 copy std)
  (NNH8_Acceptance.a5 L0 copy std _)
  (fun c => NNE_EntryArgs.count c.i.entry 3 CPH_Program.verifier c.i.data)
  (fun c => NNE_EntryArgs.count c.j.entry 7 CPH_Program.verifier c.j.data)
  (X (Tx := Tx) L0 copy std) fx w H queries run
#print axioms deployed_splitB_of
end AspisR1.NNH8_Physical
namespace AspisR1.NNH8_Top
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH8_TopHost
open NNH_Run6Installed
variable {W Tx : Type}
/-- CONDITIONAL only. Exactly A1, A2 and Split.rest remain explicit obligations.
No row credit, condition-(4) verdict or final headline is asserted. -/
theorem deployed_splitB_of
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NOC_Run5bCtx.Fixed) (w : NOC_Run5bCtx.World W Tx)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (run : Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx w H)) :
 let c := ctxB (X (Tx := Tx) L0 copy std) fx w H
 (S (Tx := Tx) L0 copy std).Bound c ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∧
 NNH8_Split.rest L0 copy c ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∧
 ((NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec c
  ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) ∨ (X (Tx := Tx) L0 copy std).ERec fx H) := by
 exact NNH8_Physical.deployed_splitB_of L0 borrow copy std
  (implementation allocation217 allocation234 ch alloc1 alloc2)
  allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx w H queries run

#print axioms deployed_splitB_of
end AspisR1.NNH8_Top
namespace AspisR1.NNH8_Numeric
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH8_TopHost
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {W Tx : Type}
/-- Existing failureModel-to-total chain, on normalize a, at every actual pair. -/
theorem host_bound
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (fx : NOC_Run5bCtx.Fixed) (w : NOC_Run5bCtx.World W Tx) (H : Bytes → State)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx) :
 let c := RSL.TASB.ctxB (X (Tx := Tx) L0 copy std) fx w H
 F3T_RuntimeBound.failureModel (NOC_Run5bHost.runtime L0 copy c
  ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c)) ≤
 F3T_Numeric.total (fx.Q0+fx.Q1) := by
 let c := RSL.TASB.ctxB (X (Tx := Tx) L0 copy std) fx w H
 have ext := (NOC_Run5bHost.a0 L0 copy std).extraction c
  ((X (Tx := Tx) L0 copy std).exhibited_mk _ _ _ _ _)
 have q : (S (Tx := Tx) L0 copy std).Queries c ((S (Tx := Tx) L0 copy std).model1 c) := queries H
 exact ((NNH8_Headline.headline L0 borrow copy std).numeric c _ _ ext q).1
#print axioms host_bound
end AspisR1.NNH8_Numeric

namespace AspisR1.NNH8_Outer
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH8_TopHost NNH_Run6Installed
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {W Tx : Type}
theorem inclusion
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NOC_Run5bCtx.Fixed)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → State) → NOC_Run5bCtx.World W Tx) (H : AspisV8R19.DuplexFrames.Bytes → State)
 (fail : (Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((S (Tx := Tx) L0 copy std).model1 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((S (Tx := Tx) L0 copy std).model2 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)))) : (X (Tx := Tx) L0 copy std).ERec fx H := by
 rcases (NNH8_Top.deployed_splitB_of L0 borrow copy std
  allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx (wOf H) H queries fail.1).2.2 with o | e
 · exact absurd o fail.2
 · exact e
#print axioms inclusion
end AspisR1.NNH8_Outer

namespace AspisR1
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH8_TopHost NNH_Run6Installed
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {W Tx : Type}
/-- CONDITIONAL physical fail_sub_rec plus EVB.no_second_charge at the literal host.
The three missing field arguments are retained visibly. -/
theorem NNH8_DeployedOuterOf
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NOC_Run5bCtx.Fixed)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (r m : (AspisV8R19.DuplexFrames.Bytes → State) → Rat)
 (hm : ∀ H, 0 ≤ m H)
 (each : ∀ H, r H ≤ m H + ind ((X (Tx := Tx) L0 copy std).ERec fx H)) :
 ∀ (wOf : (AspisV8R19.DuplexFrames.Bytes → State) → NOC_Run5bCtx.World W Tx) (H : AspisV8R19.DuplexFrames.Bytes → State),
 max (r H) (ind (Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((S (Tx := Tx) L0 copy std).model1 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((S (Tx := Tx) L0 copy std).model2 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤ m H + ind ((X (Tx := Tx) L0 copy std).ERec fx H) := by
 classical
 intro wOf H
 rw [ind_def,ind_def]
 have e := each H
 rw [ind_def] at e
 exact RSL.EVB.no_second_charge (r H) (m H) _ _ (hm H) e
  (fun fail => NNH8_Outer.inclusion L0 borrow copy std
   allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx queries wOf H fail)
#print axioms NNH8_DeployedOuterOf
end AspisR1
namespace AspisR1.NNH8_ChargeOf
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries NNH8_TopHost NNH_Run6Installed
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open FS FS2
variable {W Tx : Type}
/-- CONDITIONAL outer-envelope certificate. The SAME finite recorder event
bounds every actual failure pointwise and has the single adopted charge.
No expectation on an arbitrary World-dependent indicator is invented. -/
theorem deployed_charge_of
 (L0 : Library W (Nat → Record)) (borrow : S2TrustedSdkBorrow L0)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
 (allocation217 : RSL.Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (a1 : NND_A1 (S (Tx := Tx) L0 copy std) VL P C)
 (a2 : NND_A2 (S (Tx := Tx) L0 copy std) L D V0)
 (rest : RestLaw (Tx := Tx) L0 copy std)
 (fx : NOC_Run5bCtx.Fixed) (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (queries : (X (Tx := Tx) L0 copy std).QueriesF fx)
 (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → NOC_Run5bCtx.World W Tx) :
 (∀ H, max (0:Rat) (ind (Runs (S (Tx := Tx) L0 copy std) (implementation allocation217 allocation234 ch alloc1 alloc2)
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H) ∧
 ¬ (NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec
  (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)
  ((S (Tx := Tx) L0 copy std).model1 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H))
  ((S (Tx := Tx) L0 copy std).model2 (ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H)))) ≤ ind (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
   (eval H (NNH8_RecorderFixed.fixedProgram copy fx anchor)))) ∧
 lazyMean (NNH8_RecorderFixed.fixedProgram copy fx anchor) emptyTable
  (fun v => AspisV8R19.CausalFirstHitUnionBound.indicator
   (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965) v))
 ≤ F3T_Numeric.total (fx.Q0+fx.Q1) ∧
 (∀ H, let c := ctxB (X (Tx := Tx) L0 copy std) fx (wOf H) H
  F3T_RuntimeBound.failureModel (NOC_Run5bHost.runtime L0 copy c
   ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c)) ≤
  F3T_Numeric.total (fx.Q0+fx.Q1)) := by
 classical
 have each : ∀ H, (0:Rat) ≤ 0 + ind ((X (Tx := Tx) L0 copy std).ERec fx H) := by
  intro H
  rw [ind_def]
  split <;> norm_num
 have outer := NNH8_DeployedOuterOf L0 borrow copy std
  allocation217 allocation234 ch alloc1 alloc2 a1 a2 rest fx queries
  (fun _ => 0) (fun _ => 0) (fun _ => (show (0:Rat) ≤ 0 from Rat.le_refl)) each
 refine ⟨?_,(NNH8_HostCharge.bound copy fx anchor).trans (NNH_Run6Numeric.charge_le_total _),?_⟩
 · intro H
   have h := outer wOf H
   have same : (X (Tx := Tx) L0 copy std).ERec fx H ↔
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
     (eval H (NNH8_RecorderFixed.fixedProgram copy fx anchor)) :=
    NNH8_FullSpace.same_event L0 copy std fx wOf H anchor
   simp only [Rat.zero_add,same] at h
   exact h
 · intro H
   exact NNH8_Numeric.host_bound L0 borrow copy std fx (wOf H) H queries
#print axioms deployed_charge_of
end AspisR1.NNH8_ChargeOf
end
