import PV_FN_THREAD_f170_Segments
import PV_FN_W4_CallBoundary
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f170_Row
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f170_Segments

def keySteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  entrySteps C q + dynamicSteps (entryAfter C q)
def keyAfter {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :=
  dynamicAfter C ctl programs H (entryAfter C q)
theorem keyRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (keySteps C q) q = keyAfter C ctl programs H q := by
  unfold keySteps keyAfter
  rw [PV_THR2_IntrinsicComposition.advance_add,entryRun,dynamicRun]
#print axioms keyRun

def native277Call : PV_FN_W4_CallBoundary.Call := match PV_THR2_F170.node16 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => ⟨site,kind,generics,args,dest⟩
  | _ => ⟨⟨0,0,.null⟩,.null,.null,[],0⟩
def native277Rest := PV_THR2_F170.live.body.drop 17
theorem native277Shape : PV_FN_W4_CallBoundary.node native277Call :: native277Rest = afterKeyRest := rfl
def native277At {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_CallBoundary.after C native277Call native277Rest (afterKeyAfter C q)
def native277Steps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  afterKeySteps C q + PV_FN_W4_CallBoundary.steps native277Call native277Rest (afterKeyAfter C q)
theorem native277Run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (native277Steps C q) q = native277At C q := by
  unfold native277Steps native277At
  rw [PV_THR2_IntrinsicComposition.advance_add,afterKeyRun]
  exact PV_FN_W4_CallBoundary.run C ctl programs H native277Call _ _
#print axioms native277Shape
#print axioms native277Run

def native278Call : PV_FN_W4_CallBoundary.Call := match PV_THR2_F170.node20 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => ⟨site,kind,generics,args,dest⟩
  | _ => ⟨⟨0,0,.null⟩,.null,.null,[],0⟩
def native278Rest := PV_THR2_F170.live.body.drop 21
theorem native278Shape : PV_FN_W4_CallBoundary.node native278Call :: native278Rest = after277Rest := rfl
def native278At {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_CallBoundary.after C native278Call native278Rest (after277After C q)
def native278Steps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  after277Steps C q + PV_FN_W4_CallBoundary.steps native278Call native278Rest (after277After C q)
theorem native278Run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (native278Steps C q) q = native278At C q := by
  unfold native278Steps native278At
  rw [PV_THR2_IntrinsicComposition.advance_add,after277Run]
  exact PV_FN_W4_CallBoundary.run C ctl programs H native278Call _ _
#print axioms native278Shape
#print axioms native278Run

def native279Call : PV_FN_W4_CallBoundary.Call := match PV_THR2_F170.node23 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => ⟨site,kind,generics,args,dest⟩
  | _ => ⟨⟨0,0,.null⟩,.null,.null,[],0⟩
def native279Rest := PV_THR2_F170.live.body.drop 24
theorem native279Shape : PV_FN_W4_CallBoundary.node native279Call :: native279Rest = after278Rest := rfl
def native279At {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_CallBoundary.after C native279Call native279Rest (after278After C q)
def native279Steps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  after278Steps C q + PV_FN_W4_CallBoundary.steps native279Call native279Rest (after278After C q)
theorem native279Run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (native279Steps C q) q = native279At C q := by
  unfold native279Steps native279At
  rw [PV_THR2_IntrinsicComposition.advance_add,after278Run]
  exact PV_FN_W4_CallBoundary.run C ctl programs H native279Call _ _
#print axioms native279Shape
#print axioms native279Run

def native280Call : PV_FN_W4_CallBoundary.Call := match PV_THR2_F170.node30 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => ⟨site,kind,generics,args,dest⟩
  | _ => ⟨⟨0,0,.null⟩,.null,.null,[],0⟩
def native280Rest := PV_THR2_F170.block40.drop 5 ++ PV_THR2_F170.live.body.drop 26
theorem native280Shape : PV_FN_W4_CallBoundary.node native280Call :: native280Rest = errorEntryRest := rfl
def native280At {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_CallBoundary.after C native280Call native280Rest (errorEntryAfter C q)
def native280Steps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  errorEntrySteps C q + PV_FN_W4_CallBoundary.steps native280Call native280Rest (errorEntryAfter C q)
theorem native280Run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (native280Steps C q) q = native280At C q := by
  unfold native280Steps native280At
  rw [PV_THR2_IntrinsicComposition.advance_add,errorEntryRun]
  exact PV_FN_W4_CallBoundary.run C ctl programs H native280Call _ _
#print axioms native280Shape
#print axioms native280Run

def callbackCall : PV_FN_W4_CallBoundary.Call := match PV_THR2_F170.node55 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => ⟨site,kind,generics,args,dest⟩
  | _ => ⟨⟨0,0,.null⟩,.null,.null,[],0⟩
def callbackRest := PV_THR2_F170.live.body.drop 40
theorem callbackShape : PV_FN_W4_CallBoundary.node callbackCall :: callbackRest = callbackEntryRest := rfl
def callbackAt {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_CallBoundary.after C callbackCall callbackRest (callbackEntryAfter C q)
def callbackSteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  callbackEntrySteps C q + PV_FN_W4_CallBoundary.steps callbackCall callbackRest (callbackEntryAfter C q)
theorem callbackRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (callbackSteps C q) q = callbackAt C q := by
  unfold callbackSteps callbackAt
  rw [PV_THR2_IntrinsicComposition.advance_add,callbackEntryRun]
  exact PV_FN_W4_CallBoundary.run C ctl programs H callbackCall _ _
#print axioms callbackShape
#print axioms callbackRun

def matchedSteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  after279Steps C q + matchSteps (after279After C q)
def matchedAfter {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :=
  matchAfter C ctl programs H (after279After C q)
theorem matchedRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (matchedSteps C q) q = matchedAfter C ctl programs H q := by
  unfold matchedSteps matchedAfter
  rw [PV_THR2_IntrinsicComposition.advance_add,after279Run,matchRun]
#print axioms matchedRun

def droppedSteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  after280Steps C q + dropSteps (after280After C q)
def droppedAfter {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :=
  dropAfter C ctl programs H (after280After C q)
theorem droppedRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (droppedSteps C q) q = droppedAfter C ctl programs H q := by
  unfold droppedSteps droppedAfter
  rw [PV_THR2_IntrinsicComposition.advance_add,after280Run,dropRun]
#print axioms droppedRun

def errorFinishSteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  afterDropSteps C q + errorReturnSteps (afterDropAfter C q)
def errorFinishAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  errorReturnAfter C (afterDropAfter C q)
theorem errorFinishRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (errorFinishSteps C q) q = errorFinishAfter C q := by
  unfold errorFinishSteps errorFinishAfter
  rw [PV_THR2_IntrinsicComposition.advance_add,afterDropRun,errorReturnRun]
#print axioms errorFinishRun

def successFinishSteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  afterCallbackSteps C q + successReturnSteps (afterCallbackAfter C q)
def successFinishAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  successReturnAfter C (afterCallbackAfter C q)
theorem successFinishRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (successFinishSteps C q) q = successFinishAfter C q := by
  unfold successFinishSteps successFinishAfter
  rw [PV_THR2_IntrinsicComposition.advance_add,afterCallbackRun,successReturnRun]
#print axioms successFinishRun

def isError {W E : Type} (q : PV_THR2_IntrinsicState.State W E) : Prop :=
  match q.current.status with | .running c => PV_THR2_IntrinsicAtContinuation.Ready errorEntryFront c | _ => False

def branchSteps {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E)
    (n280 nDrop nCallback : Nat) (out280 outDrop outCallback : PV_THR2_IntrinsicState.State W E) : Nat := by
  classical
  exact if isError q then native280Steps C q + (n280 + (droppedSteps C out280 + (nDrop + errorFinishSteps C outDrop)))
    else callbackSteps C q + (nCallback + successFinishSteps C outCallback)
def branchAfter {W E : Type} (C : Carrier W Data) (q outDrop outCallback : PV_THR2_IntrinsicState.State W E) := by
  classical
  exact if isError q then errorFinishAfter C outDrop else successFinishAfter C outCallback

/-- Complete own-source composition with every native answer and both source
arms retained. These explicit call-boundary dependencies are PARTIAL; they
are not new endpoint premises or discharged B-y callee contracts. In particular
callback must be instantiated with actual18/207 and its explicit final Store. -/
theorem row {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E)
    (nKey n277 n278 n279 n280 nDrop nCallback : Nat)
    (outKey out277 out278 out279 out280 outDrop outCallback : PV_THR2_IntrinsicState.State W E)
    (calleeKey : PV_THR2_IntrinsicState.advance C ctl programs H nKey (keyAfter C ctl programs H q) = outKey)
    (callee277 : PV_THR2_IntrinsicState.advance C ctl programs H n277 (native277At C outKey) = out277)
    (callee278 : PV_THR2_IntrinsicState.advance C ctl programs H n278 (native278At C out277) = out278)
    (callee279 : PV_THR2_IntrinsicState.advance C ctl programs H n279 (native279At C out278) = out279)
    (callee280 : isError (matchedAfter C ctl programs H out279) →
      PV_THR2_IntrinsicState.advance C ctl programs H n280 (native280At C (matchedAfter C ctl programs H out279)) = out280)
    (calleeDrop : isError (matchedAfter C ctl programs H out279) →
      PV_THR2_IntrinsicState.advance C ctl programs H nDrop (droppedAfter C ctl programs H out280) = outDrop)
    (calleeCallback : ¬ isError (matchedAfter C ctl programs H out279) →
      PV_THR2_IntrinsicState.advance C ctl programs H nCallback (callbackAt C (matchedAfter C ctl programs H out279)) = outCallback) :
    PV_THR2_IntrinsicState.advance C ctl programs H
      (keySteps C q + (nKey + (native277Steps C outKey + (n277 + (native278Steps C out277 +
        (n278 + (native279Steps C out278 + (n279 + (matchedSteps C out279 +
          branchSteps C ctl programs H (matchedAfter C ctl programs H out279) n280 nDrop nCallback out280 outDrop outCallback))))))))) q =
    branchAfter C (matchedAfter C ctl programs H out279) outDrop outCallback := by
  classical
  rw [PV_THR2_IntrinsicComposition.advance_add,keyRun,
    PV_THR2_IntrinsicComposition.advance_add,calleeKey,
    PV_THR2_IntrinsicComposition.advance_add,native277Run,
    PV_THR2_IntrinsicComposition.advance_add,callee277,
    PV_THR2_IntrinsicComposition.advance_add,native278Run,
    PV_THR2_IntrinsicComposition.advance_add,callee278,
    PV_THR2_IntrinsicComposition.advance_add,native279Run,
    PV_THR2_IntrinsicComposition.advance_add,callee279,
    PV_THR2_IntrinsicComposition.advance_add,matchedRun]
  by_cases h : isError (matchedAfter C ctl programs H out279)
  · simp only [branchSteps,branchAfter,if_pos h]
    rw [PV_THR2_IntrinsicComposition.advance_add,native280Run,
      PV_THR2_IntrinsicComposition.advance_add,callee280 h,
      PV_THR2_IntrinsicComposition.advance_add,droppedRun,
      PV_THR2_IntrinsicComposition.advance_add,calleeDrop h]
    exact errorFinishRun C ctl programs H _
  · simp only [branchSteps,branchAfter,if_neg h]
    rw [PV_THR2_IntrinsicComposition.advance_add,callbackRun,
      PV_THR2_IntrinsicComposition.advance_add,calleeCallback h]
    exact successFinishRun C ctl programs H _
#print axioms row
set_option pp.piBinderNames true in
#print row
end PV_FN_THREAD_f170_Row
