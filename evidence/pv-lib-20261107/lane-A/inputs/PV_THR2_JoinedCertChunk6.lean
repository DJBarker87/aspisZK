import PV_THR2_Catch219ToIntrinsic
import PV_THR2_Catch220Invoke
import PV_THR2_Catch316Call410
import PV_THR2_Catch316Invoke
import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk2
import PV_THR2_JoinedCertChunk5
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_Original125Certificate
import PV_THR2_Original219Certificate
import PV_THR2_Original219Syntax
import PV_THR2_OriginalPreIntrinsicCertificate
import PV_THR2_OwnUniformBeforeCertificate
import PV_THR2_Source208SyntaxCertificate
import PV_THR2_SourceForwardSyntaxCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginal125Certificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_Original125Certificate
open PV_THR2_ScopeOriginalCatch PV_THR2_IntrinsicTraceGate
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
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2)+5)
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
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atEntry s n f b input mapValue value result actual p output tlsValue counter thread panicked arc),(PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).world,
        (((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events⟩ := by
    exact PV_THR2_ScopeOriginalCatch.original_catch base ctl _ (gate handler)
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
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginalScope125Certificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4)+2) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2) 5 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginal125Syntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginal125Certificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginal219Syntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_Original219Syntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F219.live.body.drop 6) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginal219Syntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginal219Certificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_Original219Certificate
open PV_THR2_ScopeOriginalAdapter PV_THR2_IntrinsicTraceGate
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
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5)+7)
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
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atAdapter s n f b input mapValue value result actual p output tlsValue counter thread panicked arc),(PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).world,
        (((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events⟩ := by
    exact PV_THR2_ScopeOriginalAdapter.original_adapter base ctl _ (gate handler)
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
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginal125Certificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2)+5) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5) 7 _ _ reached prior
  exact PV_THR2_JoinedCertCertOriginal219Syntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginal219Certificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalPreIntrinsicCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalPreIntrinsicCertificate
open PV_THR2_CatchOriginalReturned134 PV_THR2_IntrinsicTraceGate
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
    (arcReturned : (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc))
    (payload : Data)
    (returned : (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).answer = .returned (.ok payload)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) programs (PV_THR2_FnOnceDispatch.handler handler)
      ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1)+11)
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using arcReturned
  have returned' : (reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).answer = .returned (.ok payload) := by
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] using returned
  have guarded :
    PV_THR2_Execution.advance
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl))
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_FnOnceDispatch.handler (gate handler))
      (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (atReturned s n f b input mapValue value result actual p output tlsValue counter thread panicked arc payload),(reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).world,
        ((((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler (gate handler))
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply (gate handler) s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler (gate handler))
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply (gate handler) s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events) ++ (reply (gate handler) s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).events⟩ := by
    exact PV_THR2_CatchOriginalReturned134.original_returned base ctl _ (gate handler)
      s n f b input mapValue value result w key' mapped' error' branch' variant actual p output field address' callback' inactive tlsValue tls' counter counterReturned' thread threadReturned' panicked panickedReturned' arc arcReturned' payload returned'
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
      PV_THR2_CatchOriginalReturned134.reply,PV_THR2_CatchOriginalClassified.reply,
      PV_THR2_Catch219ReturnFromScope.reply,
      PV_THR2_Catch219Reply134.reply,
      PV_THR2_WrapRunEntryMatch.events] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
    (PV_THR2_FnOnceDispatch.handler handler) PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1)
    w _ _ _ stack (by rfl) guarded
  have prior := PV_THR2_JoinedCertCertOriginal219Certificate.run base ctl programs handler
    s n f b input mapValue value result w stack key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned
  have fuel : ((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5)+7) = (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1) := by omega
  rw [fuel] at prior
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1) 11 _ _ reached prior
  exact PV_THR2_JoinedCertDispatchSyntax.Original219CapturesSyntax.run _ _ programs
    (PV_THR2_FnOnceDispatch.handler handler) _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalPreIntrinsicCertificate

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSaved
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended translator acceptance. Hypotheses: none.
The retained saved request has its original descriptor. Consume the symbolic
saved-child adapter without evaluating a source store or selecting a reply. -/
theorem intrinsic (c : Config) (capture payload : Data) :
    PV_THR2_JoinedCertCertConfiguration.Ordinary (PV_THR2_Catch219ToIntrinsic.pending c capture payload) := by
  apply PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl
  all_goals first
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.2
#print axioms intrinsic
/-- Conditional on amended translator acceptance. Hypotheses: none.
The retained saved request has its original descriptor. Consume the symbolic
saved-child adapter without evaluating a source store or selecting a reply. -/
theorem take (s : Store Data) (a : Nat) (parents : List Frame) (p : Address) :
    PV_THR2_JoinedCertCertConfiguration.Ordinary (PV_THR2_Catch316Call410.pending s a parents p) := by
  apply PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl
  all_goals first
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.2
#print axioms take
/-- Conditional on amended translator acceptance. Hypotheses: none.
The retained saved request has its original descriptor. Consume the symbolic
saved-child adapter without evaluating a source store or selecting a reply. -/
theorem forward (s : Store Data) (a : Nat) (parents : List Frame) (payload : Data) :
    PV_THR2_JoinedCertCertConfiguration.Ordinary (PV_THR2_Catch316Invoke.pending s a parents payload) := by
  apply PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl
  all_goals first
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.2
#print axioms forward
/-- Conditional on amended translator acceptance. Hypotheses: none.
The retained saved request has its original descriptor. Consume the symbolic
saved-child adapter without evaluating a source store or selecting a reply. -/
theorem source220 (s : Store Data) (a : Nat) (parents : List Frame) (payload : Data) :
    PV_THR2_JoinedCertCertConfiguration.Ordinary (PV_THR2_Catch220Invoke.pending s a parents payload) := by
  apply PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl
  all_goals first
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.1
    | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.2
#print axioms source220
end PV_THR2_JoinedCertRegionSaved

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateAfter410
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_SourceForwardSyntaxCertificate.after410
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Retargeted exact-Packet exclusion certificate at the retained region boundary;
consume existing shape and Quiet proofs BY NAME. No store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 9
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F316.live.body.drop 8},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchQuiet.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F316.live.body.drop 16) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateAfter410

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateBefore410
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_SourceForwardSyntaxCertificate.before410
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Retargeted exact-Packet exclusion certificate at the retained region boundary;
consume existing shape and Quiet proofs BY NAME. No store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 8
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F316.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchQuiet.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F316.live.body.drop 7) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateBefore410

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource208SyntaxCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source208SyntaxCertificate
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Retargeted exact-Packet exclusion certificate at the retained region boundary;
consume existing shape and Quiet proofs BY NAME. No store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 12
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F208.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchQuiet.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F208.live.body.drop 11) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertRegionSource208SyntaxCertificate

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateCall220
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_SourceForwardSyntaxCertificate.call220
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Retargeted exact-Packet exclusion certificate at the retained region boundary;
consume existing shape and Quiet proofs BY NAME. No store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 6
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F220.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchQuiet.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F220.live.body.drop 5) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertRegionSourceForwardSyntaxCertificateCall220
