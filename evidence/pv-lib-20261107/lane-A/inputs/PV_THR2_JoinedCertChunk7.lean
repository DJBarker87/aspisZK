import PV_THR2_IntrinsicOriginalScopeInvoke
import PV_THR2_IntrinsicScopeInvoke
import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk6
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OwnUniformBeforeCertificate
import PV_THR2_Source208ForwardEnter
import PV_THR2_Source208SavedSyntax
import PV_THR2_Source220To208
import PV_THR2_TableTraceTransport

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSourceForwardTrace
open PV_EVHB_OwnerMachine
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_JoinedCertDispatchTrace
/-- Conditional on owner acceptance of amended translator. Hypothesis: the
explicit actual410 wrapper field shape. Derive the20-transition exclusion
certificate from pending11187 through pending8269 using existing run equalities
BY NAME and instruction shapes only. No source208 field shape or store reduction
is needed for exclusion. This is not an additional original-entry theorem. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (actual kind payload : Data) (w : OWNER) (es : List E) (stack : List Config)
    (shape : actual = PV_THR2_KeyValues.pack kind [payload]) :
    Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler (1+((5+1)+(1+12)))
      ⟨⟨.running (PV_THR2_Catch316Invoke.pending s a parents actual),w,es⟩,stack⟩ := by
  let carrier := PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b
  let d := PV_THR2_Source316Enter.entered s a parents actual
  let t := PV_THR2_Catch220Prepare.afterStore d.store d.frame.activation kind payload
  have c0 : Certificate carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 1
      ⟨⟨.running (PV_THR2_Catch316Invoke.pending s a parents actual),w,es⟩,stack⟩ := by
    apply PV_THR2_JoinedCertDispatchTrace.one
    intro d h
    cases h
    exact PV_THR2_JoinedCertRegionSaved.forward _ _ _ _
  have c1 : Certificate carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler (5+1) ⟨⟨.running d,w,es⟩,stack⟩ :=
    PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateCall220.run carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler _ _ _ w es stack
  have c2 : Certificate carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 1
      ⟨⟨.running (PV_THR2_Catch220Invoke.pending t d.frame.activation d.callers payload),w,es⟩,stack⟩ := by
    apply PV_THR2_JoinedCertDispatchTrace.one
    intro d h
    cases h
    exact PV_THR2_JoinedCertRegionSaved.source220 _ _ _ _
  have c3 : Certificate carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 12
      ⟨⟨.running (PV_THR2_Source220Enter.entered t d.frame.activation d.callers payload),w,es⟩,stack⟩ :=
    PV_THR2_JoinedCertRegionSource208SyntaxCertificate.run carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler _ _ _ w es stack
  have last := PV_THR2_JoinedCertDispatchTrace.append carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 1 12 _ _
    (PV_THR2_Source220Enter.run carrier ctl programs handler t d.frame.activation d.callers payload w es stack) c2 c3
  have middle := PV_THR2_JoinedCertDispatchTrace.append carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler (5+1) (1+12) _ _
    (PV_THR2_Source316Forward.run base ctl programs handler s a parents b actual kind payload w es stack shape) c1 last
  exact PV_THR2_JoinedCertDispatchTrace.append carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 1 ((5+1)+(1+12)) _ _
    (PV_THR2_Source316Enter.run carrier ctl programs handler s a parents actual w es stack) c0 middle
#print axioms run
end PV_THR2_JoinedCertRegionSourceForwardTrace

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSourceCallbackTrace
open PV_EVHB_OwnerMachine
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_JoinedCertDispatchTrace
open PV_THR2_Catch316TakenInvoke
/-- Conditional on owner acceptance of amended translator. Hypotheses: actual
source argument1 and410 returned case. Certify the18 retained callback transitions by
instruction shapes, reusing the proved prefix and reply equalities BY NAME.
No value identity, OWNER adequacy, or table exclusion premise is supplied. -/
theorem callback {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (p : Address)
    (payload : Data) (w : OWNER) (es : List E) (stack : List Config)
    (cell : s.cells ⟨a,1,[]⟩ = some (PV_STX2_TypedReferences.reference p .null))
    (returned : (PV_THR2_Catch316Reply410.reply handler (beforeTake s a p) p w).answer =
      .returned (.ok payload)) :
    Certificate (PV_THR2_EntryDynamic.carrier base b) ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
      (((5+2)+1)+(1+(8+1)))
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F316.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  let carrier := PV_THR2_EntryDynamic.carrier base b
  let before := beforeTake s a p
  let r := PV_THR2_Catch316Reply410.reply handler before p w
  let t := PV_THR2_Catch316Returned410.afterStore before a p payload
  have c0 : Certificate carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler ((5+2)+1)
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F316.live.body},parents,s⟩,w,es⟩,stack⟩ :=
    PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateBefore410.run carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler s a parents w es stack
  have c1 : Certificate carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 1
      ⟨⟨.running (PV_THR2_Catch316Call410.pending before a parents p),w,es⟩,stack⟩ := by
    apply PV_THR2_JoinedCertDispatchTrace.one
    intro d h
    cases h
    exact PV_THR2_JoinedCertRegionSaved.take _ _ _ _
  have c2 : Certificate carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler (8+1)
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F316.live.body.drop 8},parents,t⟩,
        r.world,es ++ r.events⟩,stack⟩ :=
    PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateAfter410.run carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler t a parents r.world (es ++ r.events) stack
  have last := PV_THR2_JoinedCertDispatchTrace.append carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 1 (8+1) _ _
    (PV_THR2_Intrinsic316Returned410.run carrier ctl (PV_THR2_SourceTraitDispatch.resolve programs)
      handler before a parents p payload w es stack returned) c1 c2
  exact PV_THR2_JoinedCertDispatchTrace.append carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler ((5+2)+1) (1+(8+1)) _ _
    (PV_THR2_Intrinsic316Prefix410.run base ctl
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      handler s a parents b p w es stack cell) c0 last
/-- Conditional on owner acceptance of amended translator. Hypothesis: actual
410 returned case. Certify intrinsic entry and the callback without modifying
318's meaning or any interpreter. Actual saved318 is distinct by descriptor shape. -/
theorem scope {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (c : Config) (capture initial payload : Data) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config)
    (returned :
      let d := (PV_THR2_Catch316Entry.segment c capture initial).callback
      let p := PV_THR2_Catch219IntrinsicCapture.sourcePlace c capture
      (PV_THR2_Catch316Reply410.reply handler (beforeTake d.store d.frame.activation p) p w).answer =
        .returned (.ok payload)) :
    Certificate (PV_THR2_EntryDynamic.carrier base b) ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
      (1+(((5+2)+1)+(1+(8+1))))
      ⟨⟨.running (PV_THR2_Catch219ToIntrinsic.pending c capture initial),w,es⟩,stack⟩ := by
  let carrier := PV_THR2_EntryDynamic.carrier base b
  have first : Certificate carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 1
      ⟨⟨.running (PV_THR2_Catch219ToIntrinsic.pending c capture initial),w,es⟩,stack⟩ := by
    apply PV_THR2_JoinedCertDispatchTrace.one
    intro d h
    cases h
    exact PV_THR2_JoinedCertRegionSaved.intrinsic _ _ _
  have second := callback base ctl programs handler
    (PV_THR2_Catch316Entry.segment c capture initial).callback.store
    (PV_THR2_Catch316Entry.segment c capture initial).callback.frame.activation
    (PV_THR2_Catch316Entry.segment c capture initial).callback.callers b
    (PV_THR2_Catch219IntrinsicCapture.sourcePlace c capture) payload w es
    (PV_THR2_Catch219ToIntrinsic.pending c capture initial :: stack)
    (PV_THR2_Catch316Entry.argument c capture initial) returned
  exact PV_THR2_JoinedCertDispatchTrace.append carrier ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler 1 (((5+2)+1)+(1+(8+1))) _ _
    (PV_THR2_IntrinsicScopeEntry.run carrier ctl
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      handler c capture initial w es stack) first second
#print axioms callback
#print axioms scope
end PV_THR2_JoinedCertRegionSourceCallbackTrace

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSourceScopeTrace
open PV_EVHB_OwnerMachine
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_JoinedCertDispatchTrace
/-- Conditional on owner acceptance of amended translator. Hypotheses: the
actual410 returned case and its explicit wrapper field shape. Certify ALL39
transitions from pending9196 through pending8269, composing already proved runs
BY NAME and syntax-only certificates. Original entry BEFORE9196 still needs its
certificate; this is not an original-entry execution theorem or endpoint premise. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (c : Config) (capture initial payload : Data) (b : Bool)
    (kind scopeValue : Data) (w : OWNER) (es : List E) (stack : List Config)
    (returned :
      let d := (PV_THR2_Catch316Entry.segment c capture initial).callback
      let p := PV_THR2_Catch219IntrinsicCapture.sourcePlace c capture
      (PV_THR2_Catch316Reply410.reply handler
        (PV_THR2_Catch316TakenInvoke.beforeTake d.store d.frame.activation p) p w).answer =
        .returned (.ok payload))
    (shape220 : payload = PV_THR2_KeyValues.pack kind [scopeValue]) :
    Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
      ((1+(((5+2)+1)+(1+(8+1))))+(1+((5+1)+(1+12))))
      ⟨⟨.running (PV_THR2_Catch219ToIntrinsic.pending c capture initial),w,es⟩,stack⟩ := by
  let d := (PV_THR2_Catch316Entry.segment c capture initial).callback
  let p := PV_THR2_Catch219IntrinsicCapture.sourcePlace c capture
  let before := PV_THR2_Catch316TakenInvoke.beforeTake d.store d.frame.activation p
  let r := PV_THR2_Catch316Reply410.reply handler before p w
  let t := PV_THR2_Catch316Returned410.afterStore before d.frame.activation p payload
  have first := PV_THR2_JoinedCertRegionSourceCallbackTrace.scope (PV_THR2_ThreadFields.carrier base)
    ctl programs handler c capture initial payload b w es stack returned
  have second := PV_THR2_JoinedCertRegionSourceForwardTrace.run base ctl programs handler
    (PV_THR2_Catch316PrepareInvoke.afterStore t d.frame.activation payload)
    d.frame.activation d.callers b payload kind scopeValue r.world (es ++ r.events)
    (PV_THR2_Catch219ToIntrinsic.pending c capture initial :: stack) shape220
  exact PV_THR2_JoinedCertDispatchTrace.append _ ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler (1+(((5+2)+1)+(1+(8+1))))
    (1+((5+1)+(1+12))) _ _
    (PV_THR2_IntrinsicScopeInvoke.run (PV_THR2_ThreadFields.carrier base) ctl
      (PV_THR2_SourceTraitDispatch.resolve programs) handler c capture initial payload b w es stack returned)
    first second
#print axioms run
end PV_THR2_JoinedCertRegionSourceScopeTrace

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionTable
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Retarget a proof-local
Packet exclusion certificate across an already proved source-table agreement.
No source run, store, or global invariant is re-proved. -/
theorem run {W E : Type} (C : Carrier W Data) (K : Control)
    (left right : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    {n : Nat} {p : PV_THR2_IntrinsicState.State W E}
    (trace : PV_THR2_JoinedCertDispatchTrace.Certificate C K left H n p)
    (same : ∀ k, k < n → PV_THR2_TableIntrinsic.Agree left right
      (PV_THR2_IntrinsicState.advance C K left H k p)) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K right H n p := by
  intro k hk
  have equality := PV_THR2_TableTraceTransport.run C K left right H k p
    (by intro j hj; exact same j (by omega))
  rw [equality]
  exact trace k hk
#print axioms run
end PV_THR2_JoinedCertRegionTable

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionOriginalScopeTrace
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_CatchOriginalClassified
/-- Conditional on owner acceptance of amended translator. Hypotheses: the
verbatim original source cases below. Retarget the retained original F0 prefix
and callback/forwarding certificates, then consume descriptor exclusion BY NAME
at its original boundary. No receiver, endpoint premise or store evaluation. -/
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
    PV_THR2_JoinedCertDispatchTrace.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_Source208Table.table programs) (PV_THR2_FnOnceDispatch.handler handler)
    ((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1)))))) ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ := by
  let programs := PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback))))))))))
  have boundary := PV_THR2_IntrinsicOriginalEntry.original_entry (PV_THR2_RangeLiterals.carrier base) ctl
    (PV_THR2_SourceTraitDispatch.resolve programs) handler s n f b input mapValue value result w
    key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned
  have certificate : PV_THR2_Source208TraceTransfer.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1)))))) ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ := by
    have fuel : ((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1)))))) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + ((1+(((5+2)+1)+(1+(8+1))))+(1+((5+1)+(1+12)))) := by omega
    rw [fuel]
    apply PV_THR2_Source208CertificateComposition.append _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) _ _ _ boundary
    · exact PV_THR2_OriginalPreIntrinsicCertificate.run (PV_THR2_RangeLiterals.carrier base) ctl programs handler
        s n f b input mapValue value result w [] key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned
    · exact PV_THR2_SourceScopeTrace.run (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base)) (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs
        (PV_THR2_FnOnceDispatch.handler handler)
        (PV_THR2_ScopeOriginalCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue counter thread panicked arc)
        (PV_THR2_RunClosureCapture.scopeValue (PV_THR2_WrapRunEntryCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue).frame.activation)
        payload takenPayload b kind220 scopeValue _ _ [] taken shape220
  have neutral : PV_THR2_JoinedCertDispatchTrace.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) (PV_THR2_FnOnceDispatch.handler handler)
      ((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1)))))) ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ := by
    have fuel : ((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1)))))) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + ((1+(((5+2)+1)+(1+(8+1))))+(1+((5+1)+(1+12)))) := by omega
    rw [fuel]
    apply PV_THR2_JoinedCertDispatchTrace.append _ _ (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) _ _ _ boundary
    · exact PV_THR2_JoinedCertCertOriginalPreIntrinsicCertificate.run (PV_THR2_RangeLiterals.carrier base) ctl programs handler
        s n f b input mapValue value result w [] key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned
    · exact PV_THR2_JoinedCertRegionSourceScopeTrace.run (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base)) (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs
        (PV_THR2_FnOnceDispatch.handler handler)
        (PV_THR2_ScopeOriginalCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue counter thread panicked arc)
        (PV_THR2_RunClosureCapture.scopeValue (PV_THR2_WrapRunEntryCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue).frame.activation)
        payload takenPayload b kind220 scopeValue _ _ [] taken shape220
  apply PV_THR2_JoinedCertRegionTable.run _ _ _ _ _ neutral
  intro k hk c running wait fn a args done waiting request
  exact (PV_THR2_Source208Table.away programs fn
    (certificate k hk c running wait fn a args done waiting request)).symm
#print axioms run
end PV_THR2_JoinedCertRegionOriginalScopeTrace

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource208ForwardEnter
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (d : Config) (kind closure : Data) (p : Address)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl
      (PV_THR2_Source208Table.table programs) handler 1
      ⟨⟨.running (PV_THR2_Source208Forward.pending d kind closure p),w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c h
  cases h
  apply PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl
  all_goals first
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.2
#print axioms run
end PV_THR2_JoinedCertRegionSource208ForwardEnter
