import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk2
import PV_THR2_JoinedCertChunk4
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_Original125Syntax
import PV_THR2_OriginalActiveCallSyntax
import PV_THR2_OriginalActiveCertificate
import PV_THR2_OriginalActiveChildSyntax
import PV_THR2_OriginalActiveReturnSyntax
import PV_THR2_OriginalActiveReturnedCertificate
import PV_THR2_OriginalCallbackReturnSyntax
import PV_THR2_OriginalCallerCertificate
import PV_THR2_OriginalCaptureSyntax
import PV_THR2_OriginalCapturesCertificate
import PV_THR2_OriginalGuardCertificate
import PV_THR2_OriginalScope121Certificate
import PV_THR2_OriginalScope121Syntax
import PV_THR2_OriginalScope122Certificate
import PV_THR2_OriginalScope122Syntax
import PV_THR2_OriginalScope123Certificate
import PV_THR2_OriginalScope123Syntax
import PV_THR2_OriginalScope125Certificate
import PV_THR2_OriginalScope125Syntax
import PV_THR2_OriginalScopeAggregateSyntax
import PV_THR2_OriginalScopeArcCertificate
import PV_THR2_OriginalScopeArcSyntax
import PV_THR2_OriginalScopeCallSyntax
import PV_THR2_OriginalScopeCapturesCertificate
import PV_THR2_OriginalScopeCapturesSyntax
import PV_THR2_OriginalScopeCertificate
import PV_THR2_OriginalScopeDataCertificate
import PV_THR2_OriginalScopeWrapSyntax
import PV_THR2_OriginalScopeWrappedCertificate
import PV_THR2_OriginalWithCertificate
import PV_THR2_OriginalWithMatchSyntax
import PV_THR2_OriginalWithReturnSyntax
import PV_THR2_OriginalWithTailCertificate
import PV_THR2_OriginalWithWorkerCertificate
import PV_THR2_OriginalWorkerBranchCertificate
import PV_THR2_OriginalWorkerReturnSyntax
import PV_THR2_ReturnInstructionShape
import PV_THR2_ReturnWaitingShape

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertReturnSyntaxCertificate
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
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 2
      ⟨⟨.running c,w,es⟩,stack⟩ := by
  let table := PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)
  let q := PV_THR2_Execution.step base ctl table handler c w
  have reached : PV_THR2_IntrinsicState.advance base ctl table handler 1
      ⟨⟨.running c,w,es⟩,stack⟩ = ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
    simp only [PV_THR2_IntrinsicState.advance]
    exact PV_THR2_IntrinsicCompatible.step base ctl table handler c w es stack
      (PV_THR2_IntrinsicCompatible.not_waiting c waiting)
  apply PV_THR2_JoinedCertDispatchWrapped.append base ctl programs handler 1 1 _ _ reached
  · apply PV_THR2_JoinedCertDispatchWrapped.one
    intro d running
    cases running
    exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
  · apply PV_THR2_JoinedCertDispatchWrapped.one
    intro d running
    obtain ⟨r,completed⟩ := PV_THR2_ReturnInstructionShape.execution base ctl table handler
      c w site place rest done waiting remaining d running
    exact PV_THR2_JoinedCertDispatchShapes.fresh d (PV_THR2_ReturnWaitingShape.execution base ctl table handler c w site place rest done waiting remaining d running)
#print axioms run
end PV_THR2_JoinedCertCertReturnSyntaxCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertQuietReturnCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (nodes : List Instruction) (site : Site) (place : Place)
    (rest : List PV_STX2_SliceSyntax.Node)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = nodes.map PV_STX2_SliceSyntax.Node.leaf ++
      .leaf (.ret site place) :: rest)
    (quiet : ∀ i, i ∈ nodes → PV_THR2_QuietInstructionShape.Quiet i) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler (nodes.length+2)
      ⟨⟨.running c,w,es⟩,stack⟩ := by
  induction nodes generalizing c w es with
  | nil =>
    exact PV_THR2_JoinedCertCertReturnSyntaxCertificate.run base ctl programs handler c w es stack
      site place rest done waiting remaining
  | cons i nodes ih =>
    have qi := quiet i (List.mem_cons.mpr (Or.inl rfl))
    have shape : c.frame.remaining = .leaf i :: (nodes.map PV_STX2_SliceSyntax.Node.leaf ++
        .leaf (.ret site place) :: rest) := by
      simpa only [List.map_cons,List.cons_append] using remaining
    have post := And.intro
      (PV_THR2_QuietStatusRange.execution base ctl
        (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler c w i _ done waiting shape qi)
      (PV_THR2_QuietExecutionShape.step base ctl
        (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler c w i _ done waiting shape qi)
    have certificate := PV_THR2_JoinedCertCertFreshSyntaxContinuation.run base ctl programs handler c w es stack
      (nodes.length+2) _ waiting post
      (by intro d world events nextDone nextWaiting nextRemaining
          exact ih d world events nextDone nextWaiting nextRemaining
            (by intro j hj; exact quiet j (List.mem_cons_of_mem i hj)))
    have length : 1+(nodes.length+2) = (i::nodes).length+2 := by simp only [List.length_cons]; omega
    rw [length] at certificate
    exact certificate
#print axioms run
end PV_THR2_JoinedCertCertQuietReturnCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalCallbackReturnSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalCallbackReturnSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 11
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 40},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietReturnCertificate.run base ctl programs handler instructions
    _ _ [] _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalCallbackReturnSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWithCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWithCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : ctl.variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier base b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier base b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl)
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      (((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier base b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl)
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      ((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (returned s n f b input mapValue value result actual p output),
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events⟩ := by
    exact PV_THR2_WrapRunEntryCallbackReturned.original_returning base ctl _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback'
  simp only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b)
    (PV_THR2_Scalars.control ctl) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s ((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) ((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1) 11 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalCallableCertificate.run base ctl programs
      (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value result w stack
      key mapped error branch variant actual field
  · exact PV_THR2_JoinedCertCertOriginalCallbackReturnSyntax.run _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalWithCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWithMatchSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWithMatchSyntax
open PV_THR2_FreshSyntaxCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 8
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F17.live.body.drop 7},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertFreshSyntaxCertificate.run base ctl programs handler 8 _ shape _ w es stack rfl rfl rfl
#print axioms run
end PV_THR2_JoinedCertCertOriginalWithMatchSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWithReturnSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWithReturnSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 8
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F17.live.body.drop 15},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietReturnCertificate.run base ctl programs handler instructions
    _ _ [] _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalWithReturnSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWithTailCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWithTailCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool)
    (input mapValue value result actual : Data) (p : Address) (output : Data)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs handler 16
      ⟨⟨.running (PV_THR2_WrapRunEntryWith.atWith s n f b input mapValue value result actual p output),w,es⟩,stack⟩ := by
  let c := PV_THR2_WrapRunEntryWith.atWith s n f b input mapValue value result actual p output
  let carrier := PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b
  let control := PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)
  let table := PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)
  have prep := PV_THR2_RunWithValue.prepare base ctl table handler c.store c.frame.activation
    c.callers output b w es (PV_THR2_WrapRunEntryWithFacts.cell s n f b input mapValue value result actual p output)
  have reached : PV_THR2_IntrinsicState.advance carrier control table handler 8
      ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := c.frame.activation,remaining := PV_THR2_F17.live.body.drop 15},
        c.callers,PV_THR2_RunWithValue.prepared c.store c.frame.activation output⟩,w,es⟩,stack⟩ := by
    rw [PV_THR2_FreshSyntaxLift.run carrier control programs handler 8 _
      PV_THR2_OriginalWithMatchSyntax.shape c w es stack rfl rfl rfl]
    exact congrArg (fun q => PV_THR2_IntrinsicState.State.mk q stack) prep
  exact PV_THR2_JoinedCertDispatchWrapped.append carrier control programs handler 8 8 _ _ reached
    (PV_THR2_JoinedCertCertOriginalWithMatchSyntax.run carrier control programs handler _ _ _ w es stack)
    (PV_THR2_JoinedCertCertOriginalWithReturnSyntax.run carrier control programs handler _ _ _ w es stack)
#print axioms run
end PV_THR2_JoinedCertCertOriginalWithTailCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWithWorkerCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWithWorkerCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      ((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      (((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunEntryWith.atWith s n f b input mapValue value result actual p output),
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events⟩ := by
    exact PV_THR2_WrapRunEntryWith.original_with (PV_THR2_ThreadFields.carrier base) (PV_THR2_ThreadFields.control ctl) _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback'
  simp only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11) 16 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalWithCertificate.run (PV_THR2_ThreadFields.carrier base)
      (PV_THR2_ThreadFields.control ctl) programs handler s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback
  · exact PV_THR2_JoinedCertCertOriginalWithTailCertificate.run base ctl programs
      (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value result actual p output _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalWithWorkerCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWorkerReturnSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWorkerReturnSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 4
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F2.live.body.drop 6},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietReturnCertificate.run base ctl programs handler instructions
    _ _ [] _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalWorkerReturnSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalCallerCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalCallerCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      (((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      ((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunWithToWorker.atWorker s n f b input mapValue value result actual p output),
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events⟩ := by
    exact PV_THR2_WrapRunEntryWorkerResult.original_worker base ctl _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback'
  simp only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s ((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) ((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16) 4 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalWithWorkerCertificate.run base ctl programs handler
      s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback
  · exact PV_THR2_JoinedCertCertOriginalWorkerReturnSyntax.run _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalCallerCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWorkerBranchCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWorkerBranchCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      ((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      (((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunEntryCaller.atCaller s n f b input mapValue value result actual p output),
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events⟩ := by
    exact PV_THR2_WrapRunEntryCaller.original_caller base ctl _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback'
  simp only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4) 1 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalCallerCertificate.run base ctl programs handler
      s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback
  · apply PV_THR2_JoinedCertDispatchWrapped.one
    intro d h
    cases h
    exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms run
end PV_THR2_JoinedCertCertOriginalWorkerBranchCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalActiveCallSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalActiveCallSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 6
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.block165 ++ PV_THR2_F1.live.body.drop 13},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F1.block165.drop 5 ++ PV_THR2_F1.live.body.drop 13) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalActiveCallSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalActiveCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalActiveCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).truth output = some false) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      (((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      ((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunEntryWorkerBranch.branched s n f b input mapValue value result actual p output false),
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events⟩ := by
    rw [PV_THR2_OriginalCompleteTable.table]
    have h := PV_THR2_WrapRunEntryWorkerBranch.original_branch base ctl (PV_THR2_ActiveTable.resolve (PV_THR2_ScopeChildren.resolve (PV_THR2_ScopeWrappers.resolve (PV_THR2_CatchChildren.resolve (PV_THR2_CatchPanicChild.resolve (PV_THR2_CatchTakeChild.resolve (PV_THR2_SourceTraitDispatch.resolve programs))))))) (PV_THR2_IntrinsicTraceGate.gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback'
    simpa only [inactive,PV_THR2_OriginalCompleteTable.fallback] using h
  simp only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s ((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) ((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1) 6 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalWorkerBranchCertificate.run base ctl programs handler
      s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback
  · exact PV_THR2_JoinedCertCertOriginalActiveCallSyntax.run _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalActiveCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalActiveChildSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalActiveChildSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 10
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F5.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F5.live.body.drop 9) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalActiveChildSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalActiveReturnedCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalActiveReturnedCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).truth output = some false) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      ((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      (((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunEntryActive.atActive s n f b input mapValue value result actual p output),
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events⟩ := by
    exact PV_THR2_WrapRunEntryActive.original_active base ctl _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive
  simp only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6) 10 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalActiveCertificate.run base ctl programs handler
      s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback inactive
  · exact PV_THR2_JoinedCertCertOriginalActiveChildSyntax.run _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalActiveReturnedCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalActiveReturnSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalActiveReturnSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 7
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F5.live.body.drop 9},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietReturnCertificate.run base ctl programs handler instructions
    _ _ [] _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalActiveReturnSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalGuardCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalGuardCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      (((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      ((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunEntryActiveReturned.atReturned s n f b input mapValue value result actual p output tlsValue),
        (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).events⟩ := by
    exact PV_THR2_WrapRunEntryActiveReturned.original_returning base ctl _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s ((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) ((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10) 7 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalActiveReturnedCertificate.run base ctl programs handler
      s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback inactive
  · exact PV_THR2_JoinedCertCertOriginalActiveReturnSyntax.run _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalGuardCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalCaptureSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalCaptureSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 14
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.block165.drop 5 ++ PV_THR2_F1.live.body.drop 13},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietExactCertificate.run base ctl programs handler instructions
    (PV_THR2_F1.block165.drop 19 ++ PV_THR2_F1.live.body.drop 13) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalCaptureSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalCapturesCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalCapturesCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      ((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      (((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunEntryGuard.atGuard s n f b input mapValue value result actual p output tlsValue),
        (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).events⟩ := by
    exact PV_THR2_WrapRunEntryGuard.original_guard base ctl _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7) 14 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalGuardCertificate.run base ctl programs handler
      s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback inactive tlsValue tls
  · exact PV_THR2_JoinedCertCertOriginalCaptureSyntax.run _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalCapturesCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeCallSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeCallSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.block165.drop 19 ++ PV_THR2_F1.live.body.drop 13},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F1.block165.drop 20 ++ PV_THR2_F1.live.body.drop 13) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeCallSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeCertificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      (((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)+2)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      ((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunEntryCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue),
        (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).events⟩ := by
    exact PV_THR2_WrapRunEntryCaptures.original_captures base ctl _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s ((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) ((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14) 2 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalCapturesCertificate.run base ctl programs handler
      s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback inactive tlsValue tls
  · exact PV_THR2_JoinedCertCertOriginalScopeCallSyntax.run _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScope121Syntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScope121Syntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 18
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F6.live.body.drop 17) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalScope121Syntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScope121Certificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScope121Certificate
open PV_THR2_WrapRunEntryCallbackReturned
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      programs
      (PV_THR2_FnOnceDispatch.handler handler)
      ((((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)+2)+18)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,PV_THR2_IntrinsicGateDispatch.handler,PV_THR2_IntrinsicGateShort.zero,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two,PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryCallbackReturned.reply,PV_THR2_FnOnceReply.reply,PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
      (((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)+2)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_WrapRunEntryScope.atScope s n f b input mapValue value result actual p output tlsValue),
        (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (PV_THR2_IntrinsicTraceGate.gate handler))
          s n f b input mapValue value w ++
        (reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value result actual p output w).events⟩ := by
    exact PV_THR2_WrapRunEntryScope.original_scope base ctl _ _
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier base) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)+2)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)+2) 18 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalScopeCertificate.run base ctl programs handler
      s n f b input mapValue value result w stack
      key mapped error branch variant actual p output field address callback inactive tlsValue tls
  · exact PV_THR2_JoinedCertCertOriginalScope121Syntax.run _ _ programs
      (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScope121Certificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScope122Syntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScope122Syntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 17},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F6.live.body.drop 19) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalScope122Syntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScope122Certificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScope122Certificate
open PV_THR2_ScopeOriginalReturned121 PV_THR2_IntrinsicTraceGate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue))
    (counter : Data)
    (counterReturned : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1)+3)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have counterReturned' : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using counterReturned
  have guarded :
    PV_THR2_Execution.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atReturned s n f b input mapValue value result actual p output tlsValue counter),
        (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).world,
        PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events⟩ := by
    exact PV_THR2_ScopeOriginalReturned121.original_returned base ctl _ (gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls' counter counterReturned'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginalScope121Certificate.run (PV_THR2_ScopeLiterals.carrier base) ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls
  have fuel : ((((((((((((((PV_THR2_RunEntryMatch.steps n+2)+5)+9)+1)+11)+16)+4)+1)+6)+10)+7)+14)+2)+18) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1) 3 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginalScope122Syntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScope122Certificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScope123Syntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScope123Syntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 19},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F6.live.body.drop 21) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalScope123Syntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertDispatchTypes
open PV_STX2_Syntax
/-- Exact source metadata discriminator, never a runtime value test. -/
def typeToken (d : Data) : Option (Nat × Nat) := match d with
  | .object [("Regular",.object [("kind",_),("generics",.object
      (("regions",_) :: ("types",.array [.object [("Deduplicated",.number n)]]) :: _))])] => some (0,n)
  | .object [("Regular",.object [("kind",_),("generics",.object
      (("regions",_) :: ("types",.array [.object [("HashConsedValue",.array [.number n,_])]]) :: _))])] => some (1,n)
  | _ => none
/-- Retained scope constructor1916 uses function124 at a DIFFERENT exact type.
This source descriptor remains opaque; only the Packet constructor12801 changes.
No store, pointer, reply or field representation is inspected. -/
def scopeFn : Data := match PV_THR2_F6.node25 with
  | .leaf (.call _ fn _ _ _) => fn
  | _ => .null
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Function identity alone cannot distinguish the two Arc constructors; use the
pinned emitted type token for124 and the function identities for126/222. -/
theorem scope : scopeFn ≠ PV_THR2_Source361PacketChildren.fn58 ∧
    scopeFn ≠ PV_THR2_PacketDataTable.fn126 ∧ scopeFn ≠ⱼ PV_THR2_PacketDataTable.fn222 := by
  refine ⟨?_,?_,?_,by decide⟩
  · intro h; have tokens := congrArg typeToken h; cases tokens
  · intro h; have ids := congrArg PV_THR2_OffPath.functionId h; cases ids
  · intro h; have ids := congrArg PV_THR2_OffPath.functionId h; cases ids
#print axioms scope
end PV_THR2_JoinedCertDispatchTypes

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScope123Certificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScope123Certificate
open PV_THR2_ScopeOriginalReturned122 PV_THR2_IntrinsicTraceGate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue))
    (counter : Data)
    (counterReturned : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter))
    (thread : Data)
    (threadReturned : (reply handler s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3)+3)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have counterReturned' : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using counterReturned
  have threadReturned' : (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using threadReturned
  have guarded :
    PV_THR2_Execution.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atReturned s n f b input mapValue value result actual p output tlsValue counter thread),(reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).world,
        (PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events⟩ := by
    exact PV_THR2_ScopeOriginalReturned122.original_returned base ctl _ (gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls' counter counterReturned' thread threadReturned'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginalScope122Certificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1)+3) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3) 3 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginalScope123Syntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScope123Certificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeAggregateSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeAggregateSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 1
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 21},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietExactCertificate.run base ctl programs handler instructions
    (PV_THR2_F6.live.body.drop 22) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeAggregateSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeDataCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeDataCertificate
open PV_THR2_ScopeOriginalReturned123 PV_THR2_IntrinsicTraceGate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue))
    (counter : Data)
    (counterReturned : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter))
    (thread : Data)
    (threadReturned : (PV_THR2_ScopeOriginalReturned122.reply handler s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread))
    (panicked : Data)
    (panickedReturned : (reply handler s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3)+1)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have counterReturned' : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using counterReturned
  have threadReturned' : (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using threadReturned
  have panickedReturned' : (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using panickedReturned
  have guarded :
    PV_THR2_Execution.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atReturned s n f b input mapValue value result actual p output tlsValue counter thread panicked),(reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).world,
        ((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).events⟩ := by
    exact PV_THR2_ScopeOriginalReturned123.original_returned base ctl _ (gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls' counter counterReturned' thread threadReturned' panicked panickedReturned'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginalScope123Certificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3)+3) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3) 1 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginalScopeAggregateSyntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeDataCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeArcSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeArcSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 22},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F6.live.body.drop 26) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchTypes.scope
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeArcSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeArcCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeArcCertificate
open PV_THR2_ScopeOriginalData PV_THR2_IntrinsicTraceGate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue))
    (counter : Data)
    (counterReturned : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter))
    (thread : Data)
    (threadReturned : (PV_THR2_ScopeOriginalReturned122.reply handler s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread))
    (panicked : Data)
    (panickedReturned : (PV_THR2_ScopeOriginalReturned123.reply handler s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1)+5)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have counterReturned' : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using counterReturned
  have threadReturned' : (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using threadReturned
  have panickedReturned' : (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using panickedReturned
  have guarded :
    PV_THR2_Execution.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atData s n f b input mapValue value result actual p output tlsValue counter thread panicked),(PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).world,
        ((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).events⟩ := by
    exact PV_THR2_ScopeOriginalData.original_data base ctl _ (gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls' counter counterReturned' thread threadReturned' panicked panickedReturned'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginalScopeDataCertificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3)+1) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1) 5 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginalScopeArcSyntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeArcCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeCapturesSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeCapturesSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 15
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 26},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietExactCertificate.run base ctl programs handler instructions
    (PV_THR2_F6.live.body.drop 41) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeCapturesSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeCapturesCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeCapturesCertificate
open PV_THR2_ScopeOriginalArcReturned PV_THR2_IntrinsicTraceGate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).truth output = some false)
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
    (arcReturned : (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1)+15)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have counterReturned' : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using counterReturned
  have threadReturned' : (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using threadReturned
  have panickedReturned' : (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using panickedReturned
  have arcReturned' : (PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using arcReturned
  have guarded :
    PV_THR2_Execution.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atReturned s n f b input mapValue value result actual p output tlsValue counter thread panicked arc),(reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).world,
        (((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events⟩ := by
    exact PV_THR2_ScopeOriginalArcReturned.original_returned base ctl _ (gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls' counter counterReturned' thread threadReturned' panicked panickedReturned' arc arcReturned'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginalScopeArcCertificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1)+5) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1) 15 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginalScopeCapturesSyntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeCapturesCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeWrapSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeWrapSyntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 4
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 41},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietExactCertificate.run base ctl programs handler instructions
    (PV_THR2_F6.live.body.drop 45) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeWrapSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScopeWrappedCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScopeWrappedCertificate
open PV_THR2_ScopeOriginalCaptures PV_THR2_IntrinsicTraceGate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).truth output = some false)
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
    (arcReturned : (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15)+4)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have counterReturned' : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using counterReturned
  have threadReturned' : (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using threadReturned
  have panickedReturned' : (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using panickedReturned
  have arcReturned' : (PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using arcReturned
  have guarded :
    PV_THR2_Execution.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atCaptures s n f b input mapValue value result actual p output tlsValue counter thread panicked arc),(PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).world,
        (((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events⟩ := by
    exact PV_THR2_ScopeOriginalCaptures.original_captures base ctl _ (gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls' counter counterReturned' thread threadReturned' panicked panickedReturned' arc arcReturned'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginalScopeCapturesCertificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1)+15) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15) 4 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginalScopeWrapSyntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScopeWrappedCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScope125Syntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScope125Syntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 45},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F6.live.body.drop 46) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalScope125Syntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalScope125Certificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalScope125Certificate
open PV_THR2_ScopeOriginalWrapped PV_THR2_IntrinsicTraceGate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).truth output = some false)
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
    (arcReturned : (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4)+2)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b w).answer = .returned (.ok input) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler)) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using branch
  have address' : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler (gate handler))
        s n f b input mapValue value w).world actual = some p := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using address
  have callback' : (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).answer =
      .returned (.ok output) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using callback
  have tls' : (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using tls
  have counterReturned' : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using counterReturned
  have threadReturned' : (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using threadReturned
  have panickedReturned' : (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using panickedReturned
  have arcReturned' : (PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc) := by
    simpa only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using arcReturned
  have guarded :
    PV_THR2_Execution.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atCall s n f b input mapValue value result actual p output tlsValue counter thread panicked arc),(PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).world,
        (((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events⟩ := by
    exact PV_THR2_ScopeOriginalWrapped.original_wrapped base ctl _ (gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls' counter counterReturned' thread threadReturned' panicked panickedReturned' arc arcReturned'
  simp only [Option.getD,
      PV_THR2_IntrinsicGateDispatch.handler,
      PV_THR2_IntrinsicGateShort.zero,
      PV_THR2_IntrinsicGateShort.one,
      PV_THR2_IntrinsicGateShort.two,
      PV_THR2_RunEntryReturned.keyReply,
      PV_THR2_RunEntryNext.mapReply,
      PV_THR2_RunEntryErrorReply.errorReply,
      PV_THR2_WrapRunEntryBranchReply.branchReply,
      PV_THR2_WrapRunEntryCallbackReturned.reply,
      PV_THR2_FnOnceReply.reply,
      PV_THR2_WrapRunEntryActiveChild.reply,
      PV_THR2_WrapRunEntryActiveRequest.atRequest,
      PV_THR2_ActiveRequest.pending,
      PV_THR2_ScopeReply121.reply,
      PV_THR2_ScopeOriginalReturned122.reply,
      PV_THR2_ScopeReply122.reply,
      PV_THR2_ScopeOriginalReturned123.reply,
      PV_THR2_ScopeReply123.reply,
      PV_THR2_ScopeOriginalArcReturned.reply,
      PV_THR2_ScopeArcReturned.reply,
      PV_THR2_ScopeArcReply.reply,
      PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginalScopeWrappedCertificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15)+4) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4) 2 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginalScope125Syntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalScope125Certificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginal125Syntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_Original125Syntax
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F125.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F125.live.body.drop 4) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginal125Syntax
