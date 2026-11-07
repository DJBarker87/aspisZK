import PV_FN_W4_OwnChain
import PV_THR2_IntrinsicAtContinuation
import PV_FN_W4_ReturnBoundary
import PV_FN_W4_One
import PV_THR2_F170
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f170_Segments
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_W4_OwnChain
/-- Syntax certificate builder. Every use is checked against the complete source
node list by shape; the unsupported fallback cannot silently remove a node. -/
def prepend (n : PV_STX2_SliceSyntax.Node) (tail : Chain) : Chain := match n with
  | .leaf (.storage site live slot) => .storage site live slot tail
  | .leaf (.bind site dst expr) => .bind site dst expr tail
  | .leaf (.aggregateMove site dst kind args) => .aggregate site dst kind args tail
  | _ => .done


def entry : Chain := (prepend PV_THR2_F170.node0 (prepend PV_THR2_F170.node1 (prepend PV_THR2_F170.node2 (prepend PV_THR2_F170.node3 (prepend PV_THR2_F170.node4 (prepend PV_THR2_F170.node5 (prepend PV_THR2_F170.node6 (prepend PV_THR2_F170.node7 (prepend PV_THR2_F170.node8 (prepend PV_THR2_F170.node9 (prepend PV_THR2_F170.node10 (prepend PV_THR2_F170.node11 (prepend PV_THR2_F170.node12 .done)))))))))))))
def entryFront := PV_THR2_F170.live.body
def entryRest := PV_THR2_F170.live.body.drop 13
theorem entryShape : nodes entry ++ entryRest = entryFront := rfl

def entryCost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w entry c.store

def entryFinish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops entryRest w entry c.store,w,es⟩,stack⟩

def entrySteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps entryFront (entryCost C) q

def entryAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after entryFront (entryFinish C) q

theorem entryRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (entrySteps C q) q = entryAfter C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w entry s)
    ⟨⟨.running ⟨{activation := a,remaining := entryFront,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← entryShape]
  exact PV_FN_W4_OwnChain.run C ctl programs H entry s a parents loops _ w es stack
#print axioms entryShape
#print axioms entryRun

def afterKey : Chain := (prepend PV_THR2_F170.node14 (prepend PV_THR2_F170.node15 .done))
def afterKeyFront := PV_THR2_F170.live.body.drop 14
def afterKeyRest := PV_THR2_F170.live.body.drop 16
theorem afterKeyShape : nodes afterKey ++ afterKeyRest = afterKeyFront := rfl

def afterKeyCost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w afterKey c.store

def afterKeyFinish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops afterKeyRest w afterKey c.store,w,es⟩,stack⟩

def afterKeySteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps afterKeyFront (afterKeyCost C) q

def afterKeyAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after afterKeyFront (afterKeyFinish C) q

theorem afterKeyRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (afterKeySteps C q) q = afterKeyAfter C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w afterKey s)
    ⟨⟨.running ⟨{activation := a,remaining := afterKeyFront,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← afterKeyShape]
  exact PV_FN_W4_OwnChain.run C ctl programs H afterKey s a parents loops _ w es stack
#print axioms afterKeyShape
#print axioms afterKeyRun

def after277 : Chain := (prepend PV_THR2_F170.node17 (prepend PV_THR2_F170.node18 (prepend PV_THR2_F170.node19 .done)))
def after277Front := PV_THR2_F170.live.body.drop 17
def after277Rest := PV_THR2_F170.live.body.drop 20
theorem after277Shape : nodes after277 ++ after277Rest = after277Front := rfl

def after277Cost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w after277 c.store

def after277Finish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops after277Rest w after277 c.store,w,es⟩,stack⟩

def after277Steps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps after277Front (after277Cost C) q

def after277After {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after after277Front (after277Finish C) q

theorem after277Run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (after277Steps C q) q = after277After C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w after277 s)
    ⟨⟨.running ⟨{activation := a,remaining := after277Front,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← after277Shape]
  exact PV_FN_W4_OwnChain.run C ctl programs H after277 s a parents loops _ w es stack
#print axioms after277Shape
#print axioms after277Run

def after278 : Chain := (prepend PV_THR2_F170.node21 (prepend PV_THR2_F170.node22 .done))
def after278Front := PV_THR2_F170.live.body.drop 21
def after278Rest := PV_THR2_F170.live.body.drop 23
theorem after278Shape : nodes after278 ++ after278Rest = after278Front := rfl

def after278Cost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w after278 c.store

def after278Finish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops after278Rest w after278 c.store,w,es⟩,stack⟩

def after278Steps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps after278Front (after278Cost C) q

def after278After {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after after278Front (after278Finish C) q

theorem after278Run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (after278Steps C q) q = after278After C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w after278 s)
    ⟨⟨.running ⟨{activation := a,remaining := after278Front,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← after278Shape]
  exact PV_FN_W4_OwnChain.run C ctl programs H after278 s a parents loops _ w es stack
#print axioms after278Shape
#print axioms after278Run

def after279 : Chain := (prepend PV_THR2_F170.node24 .done)
def after279Front := PV_THR2_F170.live.body.drop 24
def after279Rest := PV_THR2_F170.live.body.drop 25
theorem after279Shape : nodes after279 ++ after279Rest = after279Front := rfl

def after279Cost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w after279 c.store

def after279Finish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops after279Rest w after279 c.store,w,es⟩,stack⟩

def after279Steps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps after279Front (after279Cost C) q

def after279After {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after after279Front (after279Finish C) q

theorem after279Run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (after279Steps C q) q = after279After C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w after279 s)
    ⟨⟨.running ⟨{activation := a,remaining := after279Front,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← after279Shape]
  exact PV_FN_W4_OwnChain.run C ctl programs H after279 s a parents loops _ w es stack
#print axioms after279Shape
#print axioms after279Run

def errorEntry : Chain := (prepend PV_THR2_F170.node26 (prepend PV_THR2_F170.node27 (prepend PV_THR2_F170.node28 (prepend PV_THR2_F170.node29 .done))))
def errorEntryFront := PV_THR2_F170.block40 ++ PV_THR2_F170.live.body.drop 26
def errorEntryRest := PV_THR2_F170.block40.drop 4 ++ PV_THR2_F170.live.body.drop 26
theorem errorEntryShape : nodes errorEntry ++ errorEntryRest = errorEntryFront := rfl

def errorEntryCost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w errorEntry c.store

def errorEntryFinish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops errorEntryRest w errorEntry c.store,w,es⟩,stack⟩

def errorEntrySteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps errorEntryFront (errorEntryCost C) q

def errorEntryAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after errorEntryFront (errorEntryFinish C) q

theorem errorEntryRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (errorEntrySteps C q) q = errorEntryAfter C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w errorEntry s)
    ⟨⟨.running ⟨{activation := a,remaining := errorEntryFront,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← errorEntryShape]
  exact PV_FN_W4_OwnChain.run C ctl programs H errorEntry s a parents loops _ w es stack
#print axioms errorEntryShape
#print axioms errorEntryRun

def after280 : Chain := (prepend PV_THR2_F170.node31 (prepend PV_THR2_F170.node32 (prepend PV_THR2_F170.node33 (prepend PV_THR2_F170.node34 .done))))
def after280Front := PV_THR2_F170.block40.drop 5 ++ PV_THR2_F170.live.body.drop 26
def after280Rest := PV_THR2_F170.block40.drop 9 ++ PV_THR2_F170.live.body.drop 26
theorem after280Shape : nodes after280 ++ after280Rest = after280Front := rfl

def after280Cost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w after280 c.store

def after280Finish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops after280Rest w after280 c.store,w,es⟩,stack⟩

def after280Steps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps after280Front (after280Cost C) q

def after280After {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after after280Front (after280Finish C) q

theorem after280Run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (after280Steps C q) q = after280After C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w after280 s)
    ⟨⟨.running ⟨{activation := a,remaining := after280Front,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← after280Shape]
  exact PV_FN_W4_OwnChain.run C ctl programs H after280 s a parents loops _ w es stack
#print axioms after280Shape
#print axioms after280Run

def afterDrop : Chain := (prepend PV_THR2_F170.node36 (prepend PV_THR2_F170.node37 (prepend PV_THR2_F170.node38 .done)))
def afterDropFront := PV_THR2_F170.block40.drop 10 ++ PV_THR2_F170.live.body.drop 26
def afterDropRest := [PV_THR2_F170.node39] ++ PV_THR2_F170.live.body.drop 26
theorem afterDropShape : nodes afterDrop ++ afterDropRest = afterDropFront := rfl

def afterDropCost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w afterDrop c.store

def afterDropFinish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops afterDropRest w afterDrop c.store,w,es⟩,stack⟩

def afterDropSteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps afterDropFront (afterDropCost C) q

def afterDropAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after afterDropFront (afterDropFinish C) q

theorem afterDropRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (afterDropSteps C q) q = afterDropAfter C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w afterDrop s)
    ⟨⟨.running ⟨{activation := a,remaining := afterDropFront,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← afterDropShape]
  exact PV_FN_W4_OwnChain.run C ctl programs H afterDrop s a parents loops _ w es stack
#print axioms afterDropShape
#print axioms afterDropRun

def callbackEntry : Chain := (prepend PV_THR2_F170.node42 (prepend PV_THR2_F170.node43 (prepend PV_THR2_F170.node44 (prepend PV_THR2_F170.node45 (prepend PV_THR2_F170.node46 (prepend PV_THR2_F170.node47 (prepend PV_THR2_F170.node48 (prepend PV_THR2_F170.node49 (prepend PV_THR2_F170.node50 (prepend PV_THR2_F170.node51 (prepend PV_THR2_F170.node52 (prepend PV_THR2_F170.node53 (prepend PV_THR2_F170.node54 .done)))))))))))))
def callbackEntryFront := PV_THR2_F170.live.body.drop 26
def callbackEntryRest := PV_THR2_F170.live.body.drop 39
theorem callbackEntryShape : nodes callbackEntry ++ callbackEntryRest = callbackEntryFront := rfl

def callbackEntryCost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w callbackEntry c.store

def callbackEntryFinish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops callbackEntryRest w callbackEntry c.store,w,es⟩,stack⟩

def callbackEntrySteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps callbackEntryFront (callbackEntryCost C) q

def callbackEntryAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after callbackEntryFront (callbackEntryFinish C) q

theorem callbackEntryRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (callbackEntrySteps C q) q = callbackEntryAfter C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w callbackEntry s)
    ⟨⟨.running ⟨{activation := a,remaining := callbackEntryFront,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← callbackEntryShape]
  exact PV_FN_W4_OwnChain.run C ctl programs H callbackEntry s a parents loops _ w es stack
#print axioms callbackEntryShape
#print axioms callbackEntryRun

def afterCallback : Chain := (prepend PV_THR2_F170.node56 (prepend PV_THR2_F170.node57 (prepend PV_THR2_F170.node58 (prepend PV_THR2_F170.node59 (prepend PV_THR2_F170.node60 (prepend PV_THR2_F170.node61 (prepend PV_THR2_F170.node62 (prepend PV_THR2_F170.node63 (prepend PV_THR2_F170.node64 .done)))))))))
def afterCallbackFront := PV_THR2_F170.live.body.drop 40
def afterCallbackRest := PV_THR2_F170.live.body.drop 49
theorem afterCallbackShape : nodes afterCallback ++ afterCallbackRest = afterCallbackFront := rfl

def afterCallbackCost {W : Type} (C : Carrier W Data) (c : Config) (w : W) :=
  steps C c.frame.activation w afterCallback c.store

def afterCallbackFinish {W E : Type} (C : Carrier W Data) (c : Config) (w : W)
    (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨result C c.frame.activation c.callers c.frame.loops afterCallbackRest w afterCallback c.store,w,es⟩,stack⟩

def afterCallbackSteps {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps afterCallbackFront (afterCallbackCost C) q

def afterCallbackAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after afterCallbackFront (afterCallbackFinish C) q

theorem afterCallbackRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (afterCallbackSteps C q) q = afterCallbackAfter C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H (steps C a w afterCallback s)
    ⟨⟨.running ⟨{activation := a,remaining := afterCallbackFront,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← afterCallbackShape]
  exact PV_FN_W4_OwnChain.run C ctl programs H afterCallback s a parents loops _ w es stack
#print axioms afterCallbackShape
#print axioms afterCallbackRun

def dynamicFront := PV_THR2_F170.live.body.drop 13
theorem dynamicShape : dynamicFront = PV_THR2_F170.node13 :: (PV_THR2_F170.live.body.drop 14) := rfl

def dynamicSteps {W E : Type} (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_One.steps dynamicFront q

def dynamicAfter {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_One.after C ctl programs H dynamicFront q

theorem dynamicRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (dynamicSteps q) q = dynamicAfter C ctl programs H q :=
  PV_FN_W4_One.run C ctl programs H dynamicFront q
#print axioms dynamicShape
#print axioms dynamicRun

def matchFront := PV_THR2_F170.live.body.drop 25
theorem matchShape : matchFront = PV_THR2_F170.node41 :: (PV_THR2_F170.live.body.drop 26) := rfl

def matchSteps {W E : Type} (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_One.steps matchFront q

def matchAfter {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_One.after C ctl programs H matchFront q

theorem matchRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (matchSteps q) q = matchAfter C ctl programs H q :=
  PV_FN_W4_One.run C ctl programs H matchFront q
#print axioms matchShape
#print axioms matchRun

def dropFront := PV_THR2_F170.block40.drop 9 ++ PV_THR2_F170.live.body.drop 26
theorem dropShape : dropFront = PV_THR2_F170.node35 :: (PV_THR2_F170.block40.drop 10 ++ PV_THR2_F170.live.body.drop 26) := rfl

def dropSteps {W E : Type} (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_One.steps dropFront q

def dropAfter {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :=
  PV_FN_W4_One.after C ctl programs H dropFront q

theorem dropRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (dropSteps q) q = dropAfter C ctl programs H q :=
  PV_FN_W4_One.run C ctl programs H dropFront q
#print axioms dropShape
#print axioms dropRun

def errorReturnSite : Site := match PV_THR2_F170.node39 with
  | .leaf (.ret site _) => site | _ => ⟨0,0,.null⟩
def errorReturnFront := [PV_THR2_F170.node39] ++ (PV_THR2_F170.live.body.drop 26)
theorem errorReturnShape : errorReturnFront = .leaf (.ret errorReturnSite (.local 0)) :: (PV_THR2_F170.live.body.drop 26) := rfl

def errorReturnCost (c : Config) := 1 + PV_FN_W4_ReturnBoundary.extra c.store c.frame.activation c.callers

def errorReturnFinish {W E : Type} (C : Carrier W Data) (c : Config) (w : W) (es : List E)
    (stack : List Config) :=
  PV_FN_W4_ReturnBoundary.after C c.store c.frame.activation c.callers c.frame.loops errorReturnSite (PV_THR2_F170.live.body.drop 26) w es stack

def errorReturnSteps {W E : Type} (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps errorReturnFront (fun c _ => errorReturnCost c) q

def errorReturnAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after errorReturnFront (errorReturnFinish C) q

theorem errorReturnRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (errorReturnSteps q) q = errorReturnAfter C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H
    (1 + PV_FN_W4_ReturnBoundary.extra s a parents)
    ⟨⟨.running ⟨{activation := a,remaining := errorReturnFront,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [errorReturnShape]
  exact PV_FN_W4_ReturnBoundary.returnRun C ctl programs H s a parents loops errorReturnSite _ w es stack
#print axioms errorReturnShape
#print axioms errorReturnRun

def successReturnSite : Site := match PV_THR2_F170.node65 with
  | .leaf (.ret site _) => site | _ => ⟨0,0,.null⟩
def successReturnFront := [PV_THR2_F170.node65] ++ ([])
theorem successReturnShape : successReturnFront = .leaf (.ret successReturnSite (.local 0)) :: ([]) := rfl

def successReturnCost (c : Config) := 1 + PV_FN_W4_ReturnBoundary.extra c.store c.frame.activation c.callers

def successReturnFinish {W E : Type} (C : Carrier W Data) (c : Config) (w : W) (es : List E)
    (stack : List Config) :=
  PV_FN_W4_ReturnBoundary.after C c.store c.frame.activation c.callers c.frame.loops successReturnSite ([]) w es stack

def successReturnSteps {W E : Type} (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps successReturnFront (fun c _ => successReturnCost c) q

def successReturnAfter {W E : Type} (C : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after successReturnFront (successReturnFinish C) q

theorem successReturnRun {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (successReturnSteps q) q = successReturnAfter C q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C ctl programs H
    (1 + PV_FN_W4_ReturnBoundary.extra s a parents)
    ⟨⟨.running ⟨{activation := a,remaining := successReturnFront,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [successReturnShape]
  exact PV_FN_W4_ReturnBoundary.returnRun C ctl programs H s a parents loops successReturnSite _ w es stack
#print axioms successReturnShape
#print axioms successReturnRun
end PV_FN_THREAD_f170_Segments
