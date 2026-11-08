import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk7
import PV_THR2_JoinedCertChunk8
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OperatorRetainedEntry164Trace
import PV_THR2_OperatorRetainedPending8269Boundary
import PV_THR2_OwnUniformOriginalEntry164
import PV_THR2_OwnUniformSource15Call164
import PV_THR2_OwnUniformSource164OwnPrefix
import PV_THR2_OwnUniformSource164Prologue
import PV_THR2_ReturnInstructionShape
import PV_THR2_ReturnWaitingShape
import PV_THR2_Source15Call164
import PV_THR2_Source164OwnPrefix
import PV_THR2_Source164Prologue

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15Call164
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 4},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertRegionStaticSyntaxCertificate.run base ctl programs handler _ w es stack
    _ _ _ _ _ _ _ rfl rfl rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms run
end PV_THR2_JoinedCertRegionSource15Call164

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionEntry164Trace
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on amended-translator acceptance. Retarget retained D775 regions;
source boundaries consumed BY NAME, no execution or source store re-proved. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (d : Config) (kind closure : Data) (p : Address) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
      ctl (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve programs)) handler (1+(4+2))
      ⟨⟨.running (PV_THR2_Source208Forward.pending d kind closure p),w,es⟩,stack⟩ := by
  let C := PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b
  apply PV_THR2_JoinedCertDispatchTrace.append C ctl _ handler 1 (4+2) _ _
    (PV_THR2_Source208ForwardEnter.run C ctl _ handler d kind closure p w es stack)
  · exact PV_THR2_JoinedCertRegionSource208ForwardEnter.run C ctl _ handler d kind closure p w es stack
  · apply PV_THR2_JoinedCertDispatchTrace.append C ctl _ handler 4 2 _ _
      (PV_THR2_Source15Start.run (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base)) ctl _ handler d kind closure p b w es stack)
    · exact PV_THR2_JoinedCertRegionSource15Start.run C ctl _ handler _ _ _ w es stack
    · exact PV_THR2_JoinedCertRegionSource15Call164.run C ctl _ handler _ _ _ w es stack
#print axioms run
end PV_THR2_JoinedCertRegionEntry164Trace

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionOriginalEntry164
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_CatchOriginalClassified
/-- Conditional on amended-translator acceptance. Retarget the existing original
composition certificate. Both source boundaries are reused BY NAME; no source
execution, receiver, payload, or store is re-proved or assumed. -/
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
    PV_THR2_JoinedCertDispatchTrace.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b) (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_Source208Table.table programs) (PV_THR2_FnOnceDispatch.handler handler)
      (((((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1))))))+1)+4)+2)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ ∧
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b) (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_Source208Table.table programs) (PV_THR2_FnOnceDispatch.handler handler)
      (((((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1))))))+1)+4)+2)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ =
      ⟨⟨.running (PV_THR2_Source15Call164.fromForward (PV_THR2_Source220To208.entered
          (PV_THR2_Source316Enter.entered
            (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
            d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace),r.world,(((((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler handler)
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply handler s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply handler s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events) ++ (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).events) ++ r.events⟩,
        [PV_THR2_Catch219ToIntrinsic.pending c capture payload]⟩
 := by
  intro programs c capture d place before r afterTake
  have source := PV_THR2_OwnUniformOriginalEntry164.run base ctl fallback handler s n f b input mapValue value result w key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned takenPayload taken kind220 scopeValue kind208 closure scopePlace shape220 shape208
  have boundary := PV_THR2_OperatorRetainedPending8269Boundary.run base ctl fallback handler s n f b input mapValue value result w key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned takenPayload taken kind220 scopeValue kind208 closure scopePlace shape220 shape208
  dsimp only at source boundary
  refine ⟨?_,source.2⟩
  have fuel : (((((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1))))))+1)+4)+2) = ((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1)))))) + (1+(4+2)) := by omega
  rw [fuel]
  apply PV_THR2_JoinedCertDispatchTrace.append (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b) (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_Source208Table.table programs) (PV_THR2_FnOnceDispatch.handler handler) ((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1)))))) (1+(4+2)) _ _ boundary
  · exact PV_THR2_JoinedCertRegionOriginalScopeTrace.run base ctl fallback handler
      s n f b input mapValue value result w key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned takenPayload taken kind220 scopeValue kind208 closure scopePlace shape220 shape208
  · exact PV_THR2_JoinedCertRegionEntry164Trace.run base _ _ _ _ _ _ _ b _ _ _
#print axioms run
end PV_THR2_JoinedCertRegionOriginalEntry164

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource164Prologue
open PV_THR2_OwnUniformSource164Prologue
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F164.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertRegionPrefix.take base ctl programs handler
    (n := instructions.length+1) ?_ 2 (by decide)
  apply PV_THR2_JoinedCertDispatchQuiet.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F164.live.body.drop 2) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertRegionSource164Prologue

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource164OwnPrefix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source164OwnPrefix
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl
      (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback))) handler ((1+1)+(1+1))
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F164.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchTrace.append base ctl _ handler (1+1) (1+1) _ _
    (PV_THR2_Source164Prologue.run base ctl _ handler s a parents w es stack)
  · exact PV_THR2_JoinedCertRegionSource164Prologue.run base ctl _ handler s a parents w es stack
  · exact PV_THR2_JoinedCertRegionStaticSyntaxCertificate.run base ctl _ handler _ w es stack
      _ _ _ _ _ _ _ rfl rfl rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms run
end PV_THR2_JoinedCertRegionSource164OwnPrefix

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionReturnSyntaxCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (site : Site) (place : Place) (rest : List PV_STX2_SliceSyntax.Node)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = .leaf (.ret site place) :: rest) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 2
      ⟨⟨.running c,w,es⟩,stack⟩ := by
  let table := programs
  let q := PV_THR2_Execution.step base ctl table handler c w
  have reached : PV_THR2_IntrinsicState.advance base ctl table handler 1
      ⟨⟨.running c,w,es⟩,stack⟩ = ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
    simp only [PV_THR2_IntrinsicState.advance]
    exact PV_THR2_IntrinsicCompatible.step base ctl table handler c w es stack
      (PV_THR2_IntrinsicCompatible.not_waiting c waiting)
  apply PV_THR2_JoinedCertDispatchTrace.append base ctl programs handler 1 1 _ _ reached
  · apply PV_THR2_JoinedCertDispatchTrace.one
    intro d running
    cases running
    exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
  · apply PV_THR2_JoinedCertDispatchTrace.one
    intro d running
    obtain ⟨r,completed⟩ := PV_THR2_ReturnInstructionShape.execution base ctl table handler
      c w site place rest done waiting remaining d running
    exact PV_THR2_JoinedCertDispatchShapes.fresh d (PV_THR2_ReturnWaitingShape.execution base ctl table handler c w site place rest done waiting remaining d running)
#print axioms run
end PV_THR2_JoinedCertRegionReturnSyntaxCertificate
