import PV_THR2_F15
import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk12
import PV_THR2_JoinedCertChunk8
import PV_THR2_JoinedCertChunk9
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OwnUniformOriginalCaptures
import PV_THR2_OwnUniformSource15AfterHandlesCaptures
import PV_THR2_OwnUniformSource15Continue93Captures
import PV_THR2_OwnUniformSource15HandlesToCaptures
import PV_THR2_OwnUniformSource15LiveCaptures
import PV_THR2_OwnUniformSource15MatchSyntax
import PV_THR2_Source15AfterHandlesCaptures
import PV_THR2_Source15Continue93Captures
import PV_THR2_Source15HandlesToCaptures
import PV_THR2_Source15LiveCaptures

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15LiveCaptures
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15LiveCaptures
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler (steps base ctl s a w)
      (PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack) := by
  unfold steps tag
  cases hr : s.cells ⟨a,8,[]⟩ with
  | none => simp only [Option.bind_none]; exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | some v =>
    simp only [Option.bind_some]
    cases hv : ctl.variant v with
    | none => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | some n =>
      cases n with
      | zero =>
        simp only
        have shape : PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack =
          ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node19 :: PV_THR2_F15.block47.drop 8,loops := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩ := by
          simp [PV_THR2_Source15LoopMatch.after,PV_THR2_IntrinsicFrameMatch.result,PV_STX2_Store.read,write,hr,hv,selectVariant,PV_THR2_F15.block20]
        rw [shape]
        apply PV_THR2_JoinedCertDispatchTrace.one
        intro c h
        cases h
        first | exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl | exact (by apply PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl; all_goals first | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).1 | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.1 | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.2)
      | succ n =>
        cases n with
        | zero =>
          simp only
          have shape : PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack =
            ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node23 :: PV_THR2_F15.node24 :: PV_THR2_F15.block47.drop 10,loops := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩ := by
            simp [PV_THR2_Source15LoopMatch.after,PV_THR2_IntrinsicFrameMatch.result,PV_STX2_Store.read,write,hr,hv,selectVariant]
            rfl
          rw [shape]
          change PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler
            (PV_THR2_IntrinsicFrameChain.steps base a w chain (write s ⟨a,9,[]⟩ none))
            ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 8,loops := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩
          rw [← PV_THR2_Source15LiveCaptures.shape]
          apply PV_THR2_JoinedCertRegionChainCertificate.run base ctl programs handler chain _ a parents _ _ w es stack
          simp only [chain,PV_THR2_Source15CaptureChain.chain,PV_THR2_Source15CaptureChain.prepend,
            PV_THR2_F15.node23,PV_THR2_F15.node24,PV_THR2_F15.node25,PV_THR2_F15.node26,
            PV_THR2_F15.node27,PV_THR2_F15.node28,PV_THR2_F15.node29,PV_THR2_F15.node30,
            PV_THR2_F15.node31,PV_THR2_F15.node32,PV_THR2_F15.node33,
            PV_THR2_OwnUniformChainCertificate.Neutral,PV_THR2_OwnUniformNeutral.instruction]
          decide
        | succ n => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
#print axioms run
end PV_THR2_JoinedCertRegionSource15LiveCaptures

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15MatchSyntax
open PV_THR2_OwnUniformSource15MatchSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 2
      ⟨⟨.running ⟨{activation := a,remaining := [PV_THR2_F15.node18,PV_THR2_F15.node22] ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchQuiet.quiet_prefix base ctl programs handler instructions (PV_THR2_F15.node22 :: rest) _ w es stack rfl rfl rfl
  · intro i h
    simp only [instructions,List.mem_cons] at h
    rcases h with rfl | bad
    all_goals first | trivial | cases bad
#print axioms run
end PV_THR2_JoinedCertRegionSource15MatchSyntax

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15Continue93Captures
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15Continue93Captures
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler (steps base ctl s a parents (reply handler s a w))
      (PV_THR2_Source15Loop93Full.after base handler s a parents w es stack) := by
  unfold PV_THR2_Source15Loop93Full.after
  dsimp only
  generalize hr : reply handler s a w = r
  have hreq : handler (PV_THR2_StaticReply.wait (PV_THR2_Source15Loop93Issue.prepared s a)
    PV_THR2_Source15RangeChild.fn93 [PV_THR2_Source15Loop93Issue.ref a] 8).request w = r := hr
  rw [hreq]
  rcases r with ⟨answer,world,events⟩
  cases answer with
  | pending => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | fault f => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | returned result =>
    cases result with
    | fail e => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | div => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | ok v =>
      change PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler
        (2 + PV_THR2_Source15LiveCaptures.steps base ctl (returnedStore s a parents v) a world) _
      rw [PV_THR2_ChildReturnedLocal.delivered base _ _ _ 8 v world events (by rfl)]
      apply PV_THR2_JoinedCertDispatchTrace.append base ctl programs handler 2 _ _ _
        (PV_THR2_Source15LoopMatch.run base ctl programs handler _ a parents world (es ++ events) stack)
      · exact PV_THR2_JoinedCertRegionSource15MatchSyntax.run base ctl programs handler _ a parents
          [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩] (PV_THR2_F15.block47.drop 8) world (es ++ events) stack
      · exact PV_THR2_JoinedCertRegionSource15LiveCaptures.run base ctl programs handler _ a parents world (es ++ events) stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15Continue93Captures

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15AfterHandlesCaptures
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15AfterHandlesCaptures
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
      ctl (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback)))
      handler (steps base b ctl handler s a parents w)
      (PV_THR2_Source15AfterHandles93.after base b handler s a parents w es stack) := by
  unfold steps
  generalize hr : PV_THR2_Source164OwnPrefix.reply handler (PV_THR2_Source15Call164.entered s a parents) w = r
  rcases r with ⟨answer,world,events⟩
  cases answer with
  | pending => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | fault f => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | returned result =>
    cases result with
    | fail e => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | div => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | ok v =>
      simp only
      generalize hq : PV_THR2_Source15RangeTo93.reply handler (PV_THR2_Source15AfterHandles93.returnedStore s a parents v) world = q
      rcases q with ⟨answer2,world2,events2⟩
      cases answer2 with
      | pending => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
      | fault f => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
      | returned result =>
        cases result with
        | fail e => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
        | div => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
        | ok iter =>
          simp only
          unfold PV_THR2_Source15AfterHandles93.after
          rw [hr]
          dsimp only
          unfold PV_THR2_Source15RangeTo93.after
          rw [hq]
          unfold PV_THR2_Source15ContinueTo93.after
          dsimp only
          exact PV_THR2_JoinedCertRegionSource15Continue93Captures.run _ ctl _ handler _ a parents world2 ((es ++ events) ++ events2) stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15AfterHandlesCaptures

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15HandlesToCaptures
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15HandlesToCaptures
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier
        (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
      ctl (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback)))
      handler (steps base b ctl handler s a parents w)
      ⟨⟨.running (PV_THR2_Source15Call164.entered s a parents),w,es⟩,stack⟩ := by
  unfold steps
  apply PV_THR2_JoinedCertDispatchTrace.append _ ctl _ handler _ _ _ _
    (PV_THR2_Source15HandlesTo93.run base ctl fallback handler s a parents b w es stack)
  · exact PV_THR2_JoinedCertRegionSource15HandlesTo93.run base ctl fallback handler s a parents b w es stack
  · exact PV_THR2_JoinedCertRegionSource15AfterHandlesCaptures.run base ctl fallback handler s a parents b w es stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15HandlesToCaptures

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionOriginalCaptures
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_CatchOriginalClassified
/-- Conditional on owner acceptance of amended translator. Hypotheses: the
verbatim original source cases below. Join the retained all-case F15 segment
to original F0; source worlds, failures and events remain exact. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : OWNER)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue))
    (counter : Data)
    (counterReturned : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter))
    (thread : Data)
    (threadReturned : (PV_THR2_ScopeOriginalReturned122.reply handler s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread))
    (panicked : Data)
    (panickedReturned : (PV_THR2_ScopeOriginalReturned123.reply handler s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked))
    (arc : Data)
    (arcReturned : (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc))
    (payload : Data)
    (returned : (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).answer = .returned (.ok payload))
    (takenPayload : Data)
    (taken :
      let c := PV_THR2_ScopeOriginalCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue counter thread panicked arc
      let capture := PV_THR2_RunClosureCapture.scopeValue (PV_THR2_WrapRunEntryCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue).frame.activation
      let d := (PV_THR2_Catch316Entry.segment c capture payload).callback
      let place := PV_THR2_Catch219IntrinsicCapture.sourcePlace c capture
      (PV_THR2_Catch316Reply410.reply (PV_THR2_FnOnceDispatch.handler handler)
        (PV_THR2_Catch316TakenInvoke.beforeTake d.store d.frame.activation place) place
        (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).world).answer = .returned (.ok takenPayload))
    (kind220 scopeValue kind208 closure : Data) (scopePlace : Address)
    (shape220 : takenPayload = PV_THR2_KeyValues.pack kind220 [scopeValue])
    (shape208 : scopeValue = PV_THR2_KeyValues.pack kind208
      [closure,PV_STX2_TypedReferences.reference scopePlace .null]) :
    let programs := PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback))))))))))
    let c := PV_THR2_ScopeOriginalCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue counter thread panicked arc
    let capture := PV_THR2_RunClosureCapture.scopeValue (PV_THR2_WrapRunEntryCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue).frame.activation
    let d := (PV_THR2_Catch316Entry.segment c capture payload).callback
    let place := PV_THR2_Catch219IntrinsicCapture.sourcePlace c capture
    let before := PV_THR2_Catch316TakenInvoke.beforeTake d.store d.frame.activation place
    let r := PV_THR2_Catch316Reply410.reply (PV_THR2_FnOnceDispatch.handler handler) before place (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).world
    let afterTake := PV_THR2_Catch316Returned410.afterStore before d.frame.activation place takenPayload
    PV_THR2_JoinedCertDispatchTrace.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b) (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_Source208Table.table programs) (PV_THR2_FnOnceDispatch.handler handler) ((((((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1))))))+1)+4)+2) + (PV_THR2_Source15HandlesToCaptures.steps base b (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).store (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).frame.activation (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).callers r.world)) ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ ∧
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b) (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_Source208Table.table programs) (PV_THR2_FnOnceDispatch.handler handler) ((((((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1))))))+1)+4)+2) + (PV_THR2_Source15HandlesToCaptures.steps base b (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).store (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).frame.activation (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).callers r.world)) ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ =
          PV_THR2_Source15AfterHandlesCaptures.after base (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) b (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).store (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).frame.activation (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).callers r.world ((((((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler handler)
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply handler s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply handler s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events) ++ (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).events) ++ r.events) ([PV_THR2_Catch219ToIntrinsic.pending c capture payload]) := by
  intro programs c capture d place before r afterTake
  have entry := PV_THR2_JoinedCertRegionOriginalEntry164.run base ctl fallback handler s n f b input mapValue value result w key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned takenPayload taken kind220 scopeValue kind208 closure scopePlace shape220 shape208
  dsimp only at entry
  constructor
  · apply PV_THR2_JoinedCertDispatchTrace.append (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b) (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_Source208Table.table programs) (PV_THR2_FnOnceDispatch.handler handler) (((((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1))))))+1)+4)+2) (PV_THR2_Source15HandlesToCaptures.steps base b (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
          (PV_THR2_Source316Enter.entered
            (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
            d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).store (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
          (PV_THR2_Source316Enter.entered
            (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
            d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).frame.activation (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
          (PV_THR2_Source316Enter.entered
            (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
            d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).callers r.world) _ _ entry.2 entry.1
    exact PV_THR2_JoinedCertRegionSource15HandlesToCaptures.run base (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) _ (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
          (PV_THR2_Source316Enter.entered
            (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
            d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).store (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
          (PV_THR2_Source316Enter.entered
            (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
            d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).frame.activation (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
          (PV_THR2_Source316Enter.entered
            (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
            d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).callers b r.world ((((((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler handler)
      s n f b input mapValue value w ++
    (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).events ++
    (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply handler s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply handler s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events) ++ (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).events) ++ r.events) ([PV_THR2_Catch219ToIntrinsic.pending c capture payload])
  · exact (PV_THR2_OwnUniformOriginalCaptures.run base ctl fallback handler s n f b input mapValue value result w key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned takenPayload taken kind220 scopeValue kind208 closure scopePlace shape220 shape208).2
#print axioms run
end PV_THR2_JoinedCertRegionOriginalCaptures
