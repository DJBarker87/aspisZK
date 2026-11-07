import PV_LIB_A_PureCalls
import PV_THR2_SourceStoreInterpreter
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PurePoll
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
private def functionId : Data → Option Nat
  | .object [("Regular",.object [("kind",.object [("Fun",.object
      [("Regular",.number n)])]),("generics",_)])] => some n
  | _ => none
/-- Small direct poll proof avoids replaying W4's 167-module full row cone.
It uses the existing full native administration theorem by name. -/
theorem unlisted_poll {E : Type} (C : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER E)
    (e : Entry) (w : OWNER) (es : List E)
    (ordinary : PV_THR2_Catch316Segment.select (pending e) = none)
    (leaf : programs e.callee = none)
    (unlisted : PV_THR2_SourceStoreNative.function e.callee = none) :
    PV_THR2_SourceStoreInterpreter.step C ctl programs
      (PV_THR2_OwnUniformResourceHandler.lift H) values
      ⟨⟨.running (pending e),w,es⟩,e.suspended⟩ =
    deliver C e (PV_THR2_OwnUniformResourceHandler.lift H
      (.child e.callee e.store.nextActivation e.arguments) w) es := by
  have outside : PV_THR2_SourceStoreNative.select programs (pending e) = none := by
    simp [PV_THR2_SourceStoreNative.select,pending,
      PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticReply.wait,leaf,unlisted]
  simp only [PV_THR2_SourceStoreInterpreter.step,ordinary,outside]
  exact PV_THR2_IntrinsicFrameFull.run C ctl programs
    (PV_THR2_OwnUniformResourceHandler.lift H) e.store e.caller e.parents e.loops
    e.rest e.callee e.arguments e.destination w es e.suspended ordinary leaf

/-- Catch interception depends on its exact function token and arity only. -/
theorem noncatch (e : Entry) (other : e.callee ≠ PV_THR2_Catch219Call318.fn) :
    PV_THR2_Catch316Segment.select (pending e) = none := by
  cases args : e.arguments with
  | nil => simp [PV_THR2_Catch316Segment.select,pending,
      PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticReply.wait,args]
  | cons first rest =>
    cases rest with
    | nil => simp [PV_THR2_Catch316Segment.select,pending,
        PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticReply.wait,args]
    | cons second rest =>
      cases rest with
      | nil => simp [PV_THR2_Catch316Segment.select,pending,
          PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticReply.wait,args]
      | cons third rest =>
        cases rest <;> simp [PV_THR2_Catch316Segment.select,pending,
          PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticReply.wait,args,other]
#print axioms unlisted_poll
#print axioms noncatch

/-- Exact CLOSED277 graph at the new interpreter's poll. Purity follows from
W4's named memory semantics, rather than selecting identity effects. -/
theorem installed277 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_AsRef277 C D)
    (ctl : Control) (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : Backend E) (values : PV_THR2_SourceStoreLibrary.Values OWNER E)
    (e : Entry) (w : OWNER) (args : List Data) (es : List E)
    (leaf : programs (PV_W1_NativeLeaves.entry277 e args).callee = none) :
    PV_LIB_A_NativeLeaves.law277 C e H w args es
      (D (PV_W1_NativeLeaves.entry277 e args) w)
      (PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs
        (PV_THR2_OwnUniformResourceHandler.lift H) values
        ⟨⟨.running (pending (PV_W1_NativeLeaves.entry277 e args)),w,es⟩,e.suspended⟩)) := by
  let d := PV_W1_NativeLeaves.entry277 e args
  have pure := PV_FN_THREAD_f170_ActualNativeFrames.pureStore C d w (D d w) (library e w args)
  have after : PV_W1_ArgumentEffects.afterEffects C d w (D d w) = d := by
    unfold PV_W1_ArgumentEffects.afterEffects
    rw [pure]
  have code : PV_THR2_SourceStoreNative.function d.callee = none := rfl
  have other : d.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    -- Inspect the distinct literal function ids, not their generic metadata.
    have ids := congrArg functionId h
    change some 277 = some 318 at ids
    cases ids
  change PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs
    (PV_THR2_OwnUniformResourceHandler.lift H) values
    ⟨⟨.running (pending d),w,es⟩,d.suspended⟩) =
    PV_LIB.observe (PV_LIB_NativeGraph.internalModel C d H w es (D d w))
  rw [unlisted_poll C ctl programs H values d w es (noncatch d other) leaf code]
  unfold PV_LIB_NativeGraph.internalModel
  rw [after]
#print axioms installed277

/-- Exact CLOSED278 graph at the new interpreter's poll. Purity follows from
W4's named memory semantics, rather than selecting identity effects. -/
theorem installed278 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_OkOr278 C D)
    (ctl : Control) (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : Backend E) (values : PV_THR2_SourceStoreLibrary.Values OWNER E)
    (e : Entry) (w : OWNER) (args : List Data) (es : List E)
    (leaf : programs (PV_W1_NativeLeaves.entry278 e args).callee = none) :
    PV_LIB_A_NativeLeaves.law278 C e H w args es
      (D (PV_W1_NativeLeaves.entry278 e args) w)
      (PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs
        (PV_THR2_OwnUniformResourceHandler.lift H) values
        ⟨⟨.running (pending (PV_W1_NativeLeaves.entry278 e args)),w,es⟩,e.suspended⟩)) := by
  let d := PV_W1_NativeLeaves.entry278 e args
  have pure := PV_FN_THREAD_f170_ActualNativeFrames.pureStore C d w (D d w) (library e w args)
  have after : PV_W1_ArgumentEffects.afterEffects C d w (D d w) = d := by
    unfold PV_W1_ArgumentEffects.afterEffects
    rw [pure]
  have code : PV_THR2_SourceStoreNative.function d.callee = none := rfl
  have other : d.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    -- Inspect the distinct literal function ids, not their generic metadata.
    have ids := congrArg functionId h
    change some 278 = some 318 at ids
    cases ids
  change PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs
    (PV_THR2_OwnUniformResourceHandler.lift H) values
    ⟨⟨.running (pending d),w,es⟩,d.suspended⟩) =
    PV_LIB.observe (PV_LIB_NativeGraph.internalModel C d H w es (D d w))
  rw [unlisted_poll C ctl programs H values d w es (noncatch d other) leaf code]
  unfold PV_LIB_NativeGraph.internalModel
  rw [after]
#print axioms installed278

/-- Exact CLOSED279 graph at the new interpreter's poll. Purity follows from
W4's named memory semantics, rather than selecting identity effects. -/
theorem installed279 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_Branch279 C D)
    (ctl : Control) (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : Backend E) (values : PV_THR2_SourceStoreLibrary.Values OWNER E)
    (e : Entry) (w : OWNER) (args : List Data) (es : List E)
    (leaf : programs (PV_W1_NativeLeaves.entry279 e args).callee = none) :
    PV_LIB_A_NativeLeaves.law279 C e H w args es
      (D (PV_W1_NativeLeaves.entry279 e args) w)
      (PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs
        (PV_THR2_OwnUniformResourceHandler.lift H) values
        ⟨⟨.running (pending (PV_W1_NativeLeaves.entry279 e args)),w,es⟩,e.suspended⟩)) := by
  let d := PV_W1_NativeLeaves.entry279 e args
  have pure := PV_FN_THREAD_f170_ActualNativeFrames.pureStore C d w (D d w) (library e w args)
  have after : PV_W1_ArgumentEffects.afterEffects C d w (D d w) = d := by
    unfold PV_W1_ArgumentEffects.afterEffects
    rw [pure]
  have code : PV_THR2_SourceStoreNative.function d.callee = none := rfl
  have other : d.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    -- Inspect the distinct literal function ids, not their generic metadata.
    have ids := congrArg functionId h
    change some 279 = some 318 at ids
    cases ids
  change PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs
    (PV_THR2_OwnUniformResourceHandler.lift H) values
    ⟨⟨.running (pending d),w,es⟩,d.suspended⟩) =
    PV_LIB.observe (PV_LIB_NativeGraph.internalModel C d H w es (D d w))
  rw [unlisted_poll C ctl programs H values d w es (noncatch d other) leaf code]
  unfold PV_LIB_NativeGraph.internalModel
  rw [after]
#print axioms installed279

/-- Exact CLOSED280 graph at the new interpreter's poll. Purity follows from
W4's named memory semantics, rather than selecting identity effects. -/
theorem installed280 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_FromResidual280 C D)
    (ctl : Control) (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : Backend E) (values : PV_THR2_SourceStoreLibrary.Values OWNER E)
    (e : Entry) (w : OWNER) (args : List Data) (es : List E)
    (leaf : programs (PV_W1_NativeLeaves.entry280 e args).callee = none) :
    PV_LIB_A_NativeLeaves.law280 C e H w args es
      (D (PV_W1_NativeLeaves.entry280 e args) w)
      (PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs
        (PV_THR2_OwnUniformResourceHandler.lift H) values
        ⟨⟨.running (pending (PV_W1_NativeLeaves.entry280 e args)),w,es⟩,e.suspended⟩)) := by
  let d := PV_W1_NativeLeaves.entry280 e args
  have pure := PV_FN_THREAD_f170_ActualNativeFrames.pureStore C d w (D d w) (library e w args)
  have after : PV_W1_ArgumentEffects.afterEffects C d w (D d w) = d := by
    unfold PV_W1_ArgumentEffects.afterEffects
    rw [pure]
  have code : PV_THR2_SourceStoreNative.function d.callee = none := rfl
  have other : d.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    -- Inspect the distinct literal function ids, not their generic metadata.
    have ids := congrArg functionId h
    change some 280 = some 318 at ids
    cases ids
  change PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs
    (PV_THR2_OwnUniformResourceHandler.lift H) values
    ⟨⟨.running (pending d),w,es⟩,d.suspended⟩) =
    PV_LIB.observe (PV_LIB_NativeGraph.internalModel C d H w es (D d w))
  rw [unlisted_poll C ctl programs H values d w es (noncatch d other) leaf code]
  unfold PV_LIB_NativeGraph.internalModel
  rw [after]
#print axioms installed280
end PV_LIB_A_PurePoll
