import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk2
import PV_THR2_JoinedCertChunk3
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OriginalBranchCertificate
import PV_THR2_OriginalBranchSyntax
import PV_THR2_OriginalCallableCertificate
import PV_THR2_OriginalCallableSyntax
import PV_THR2_OriginalDynamicCertificate
import PV_THR2_OriginalErrorCertificate
import PV_THR2_OriginalErrorSyntax
import PV_THR2_OriginalForwardCertificate
import PV_THR2_OriginalForwardSyntax
import PV_THR2_OriginalKeyRequestCertificate
import PV_THR2_OriginalMatchCertificate
import PV_THR2_OriginalMatchSyntax
import PV_THR2_OriginalNextCertificate
import PV_THR2_OriginalNextSyntax
import PV_THR2_OriginalTlsCertificate
import PV_THR2_OriginalTryCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalTlsCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalTlsCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (w : W) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_Scalars.carrier base)
      (PV_THR2_Scalars.control ctl) programs handler
      (((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)+(5+2))
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_Scalars.carrier base)
    (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
    PV_THR2_F0.live [.number n,f] s ((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)
    w w [] _ stack (by rfl)
    (PV_THR2_RunEntryWorker.original_worker base ctl _ _ s n f w)
  exact PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    ((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3) (5+2) _ _ reached
    (PV_THR2_JoinedCertCertOriginalWorkerCertificate.run base ctl programs handler s n f w stack)
    (PV_THR2_JoinedCertCertOriginalF2EarlySyntax.run _ _ programs handler _ _ _ w [] stack)
#print axioms run
end PV_THR2_JoinedCertCertOriginalTlsCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalTryCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalTryCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (w : W) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler
      ((((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)+(5+2))+(6+2))
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b)
    (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
    PV_THR2_F0.live [.number n,f] s (((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)+(5+2))
    w w [] _ stack (by rfl)
    (PV_THR2_WrapRunEntryTls.original_with (PV_THR2_KeyInstall.carrier base b) ctl _ _
      s n f (PV_THR2_KeyInitConstruct.key b) w (PV_THR2_KeyInstall.global base b w))
  exact PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    (((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)+(5+2)) (6+2) _ _ reached
    (PV_THR2_JoinedCertCertOriginalTlsCertificate.run
      (PV_STX2_TypedReferences.carrier (PV_THR2_FunctionValues.base (PV_THR2_KeyInstall.carrier base b)))
      ctl programs handler s n f w stack)
    (PV_THR2_JoinedCertCertOriginalF17EarlySyntax.run _ _ programs handler _ _ _ w [] stack)
#print axioms run
end PV_THR2_JoinedCertCertOriginalTryCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalDynamicCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalDynamicCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (w : W) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler
      (((((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)+(5+2))+(6+2))+14)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b)
    (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
    PV_THR2_F0.live [.number n,f] s ((((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)+(5+2))+(6+2))
    w w [] _ stack (by rfl)
    (PV_THR2_WrapRunEntryTryWith.original_try (PV_THR2_KeyInstall.carrier base b) ctl _ _
      s n f (PV_THR2_KeyInitConstruct.key b) w (PV_THR2_KeyInstall.global base b w))
  exact PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    ((((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)+(5+2))+(6+2)) 14 _ _ reached
    (PV_THR2_JoinedCertCertOriginalTryCertificate.run base ctl programs handler s n f b w stack)
    (PV_THR2_JoinedCertDispatchSyntax.OriginalF170EarlySyntax.run _ _ programs handler _ _ _ w [] stack)
#print axioms run
end PV_THR2_JoinedCertCertOriginalDynamicCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalKeyRequestCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalKeyRequestCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (w : W) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler
      ((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b)
    (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
    PV_THR2_F0.live [.number n,f] s (((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)
    w w [] _ stack (by rfl)
    (PV_THR2_WrapRunEntryReply.original_request base ctl _ _ s n f b w)
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    (((PV_THR2_EntryKeyLoad.steps n+1)+2)+1) 1 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalDynamicCertificate.run base ctl programs handler s n f b w stack
  · apply PV_THR2_JoinedCertDispatchWrapped.one
    intro c running
    cases running
    exact PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl (by exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)).1) (by exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)).2.1) (by exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)).2.2)
#print axioms run
end PV_THR2_JoinedCertCertOriginalKeyRequestCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertQuietExactCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (nodes : List Instruction) (tail : List PV_STX2_SliceSyntax.Node)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = nodes.map PV_STX2_SliceSyntax.Node.leaf ++ tail)
    (quiet : ∀ i, i ∈ nodes → PV_THR2_QuietInstructionShape.Quiet i) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler nodes.length
      ⟨⟨.running c,w,es⟩,stack⟩ := by
  have larger := PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler
    nodes tail c w es stack done waiting remaining quiet
  intro k hk
  exact larger k (by omega)
#print axioms run
end PV_THR2_JoinedCertCertQuietExactCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalNextSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalNextSyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 14},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F170.live.body.drop 17) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalNextSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalNextCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalNextCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (value : Data) (w : W)
    (stack : List Config)
    (answer : (PV_THR2_RunEntryReturned.keyReply handler s n f b w).answer = .returned (.ok value)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler
      (((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+4)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have answer' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).answer = .returned (.ok value) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_IntrinsicGateShort.one] using answer
  have guarded : PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl)
      (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs))
      (PV_THR2_IntrinsicTraceGate.gate handler) ((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (PV_THR2_RunEntryReturned.returned s n f b value),
        (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).world,
        (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).events⟩ := by
    exact PV_THR2_WrapRunEntryReturned.original_returning base ctl _ _ s n f b value w answer'
  simp only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_IntrinsicGateShort.one] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b)
    (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
    PV_THR2_F0.live [.number n,f] s ((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)
    w _ _ _ stack (by rfl) guarded
  exact PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    ((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1) 4 _ _ reached
    (PV_THR2_JoinedCertCertOriginalKeyRequestCertificate.run base ctl programs handler s n f b w stack)
    (PV_THR2_JoinedCertCertOriginalNextSyntax.run _ _ programs handler _ _ _ _ _ stack)
#print axioms run
end PV_THR2_JoinedCertCertOriginalNextCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalErrorSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalErrorSyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 17},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F170.live.body.drop 21) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalErrorSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalErrorCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalErrorCertificate
open PV_THR2_RunEntryError
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input value : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply handler s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply handler s n f b input w).answer = .returned (.ok value)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler
      (((((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+3)+1)+5)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).answer = .returned (.ok input) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input w).answer = .returned (.ok value) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using mapped
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) (PV_THR2_IntrinsicTraceGate.gate handler)
      ((((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+3)+1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (returned s n f b input value),
        (PV_THR2_RunEntryNext.mapReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input w).world,
        (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).events ++
          (PV_THR2_RunEntryNext.mapReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input w).events⟩ := by
    exact PV_THR2_WrapRunEntryError.original_returned base ctl _ _ s n f b input value w key' mapped'
  simp only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b) (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler PV_THR2_F0.live [.number n,f] s ((((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+3)+1)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    ((((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+3)+1) 5 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalNextCertificate.run base ctl programs handler s n f b input w stack key
  · exact PV_THR2_JoinedCertCertOriginalErrorSyntax.run _ _ programs handler _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalErrorCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalBranchSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalBranchSyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 21},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F170.live.body.drop 24) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalBranchSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalBranchCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalBranchCertificate
open PV_THR2_WrapRunEntryBranch
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply handler s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply handler s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply handler s n f b input mapValue w).answer = .returned (.ok value)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler
      (((((((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+3)+1)+4)+1)+4)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).answer = .returned (.ok input) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using error
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) (PV_THR2_IntrinsicTraceGate.gate handler)
      ((((((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+3)+1)+4)+1)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (returned s n f b input mapValue value),
        (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue w).world,
        ((PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).events ++
          (PV_THR2_RunEntryNext.mapReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input w).events) ++
          (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue w).events⟩ := by
    exact PV_THR2_WrapRunEntryBranch.original_returned base ctl _ _ s n f b input mapValue value w key' mapped' error'
  simp only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b) (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler PV_THR2_F0.live [.number n,f] s ((((((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+3)+1)+4)+1)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    ((((((((PV_THR2_EntryKeyLoad.steps n+1)+2)+1)+1)+3)+1)+4)+1) 4 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalErrorCertificate.run base ctl programs handler s n f b input mapValue w stack key mapped
  · exact PV_THR2_JoinedCertCertOriginalBranchSyntax.run _ _ programs handler _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalBranchCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalMatchSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalMatchSyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 24},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler
    [.storage ⟨170,8092,.array [.atom "body",.atom "statements",.number 24]⟩ false 5]
    (PV_THR2_F170.live.body.drop 25) _ w es stack rfl rfl
  · rfl
  · intro i h
    simp only [List.mem_singleton] at h
    subst i
    trivial
#print axioms run
end PV_THR2_JoinedCertCertOriginalMatchSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalMatchCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalMatchCertificate
open PV_THR2_WrapRunEntryMatch
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply handler s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply handler s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply handler s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply handler s n f b input mapValue value w).answer = .returned (.ok result)) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler ((PV_THR2_RunEntryMatch.steps n)+2)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).answer = .returned (.ok input) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using branch
  have guarded :
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) (PV_THR2_IntrinsicTraceGate.gate handler) (PV_THR2_RunEntryMatch.steps n)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running (returned s n f b input mapValue value result),
        (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w).world,
        events (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w⟩ := by
    exact PV_THR2_WrapRunEntryMatch.original_returned base ctl _ _ s n f b input mapValue value result w key' mapped' error' branch'
  simp only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b) (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    (PV_THR2_RunEntryMatch.steps n) 2 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalBranchCertificate.run base ctl programs handler s n f b input mapValue value w stack key mapped error
  · exact PV_THR2_JoinedCertCertOriginalMatchSyntax.run _ _ programs handler _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalMatchCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalForwardSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalForwardSyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 26},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertCertQuietExactCertificate.run base ctl programs handler instructions
    (PV_THR2_F170.live.body.drop 31) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalForwardSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalForwardCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalForwardCertificate
open PV_THR2_WrapRunEntryMatch
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply handler s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply handler s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply handler s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply handler s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : ctl.variant result = some 0) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler ((PV_THR2_RunEntryMatch.steps n+2)+5)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).answer = .returned (.ok input) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using branch
  have guarded :
    let c := PV_THR2_WrapRunEntryMatch.returned s n f b input mapValue value result
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) (PV_THR2_IntrinsicTraceGate.gate handler) (PV_THR2_RunEntryMatch.steps n+2)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      ⟨.running ⟨{activation := c.frame.activation,remaining := PV_THR2_F170.live.body.drop 26},c.callers,
        write c.store ⟨c.frame.activation,5,[]⟩ none⟩,
        (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w).world,
        events (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w⟩ := by
    exact PV_THR2_WrapRunEntryMatch.original_success base ctl _ _ s n f b input mapValue value result w key' mapped' error' branch' variant
  dsimp only at guarded
  simp only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b) (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler PV_THR2_F0.live [.number n,f] s (PV_THR2_RunEntryMatch.steps n+2)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    (PV_THR2_RunEntryMatch.steps n+2) 5 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalMatchCertificate.run base ctl programs handler s n f b input mapValue value result w stack key mapped error branch
  · exact PV_THR2_JoinedCertCertOriginalForwardSyntax.run _ _ programs handler _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalForwardCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalCallableSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalCallableSyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 31},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F170.live.body.drop 40) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalCallableSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalCallableCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalCallableCertificate
open PV_THR2_WrapRunEntryForward
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : W) (stack : List Config)
    (key : (PV_THR2_RunEntryReturned.keyReply handler s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply handler s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply handler s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply handler s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : ctl.variant result = some 0)
    (actual : Data)
    (field : (PV_THR2_EntryDynamic.carrier base b).field result 0 = some actual) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler
      (((PV_THR2_RunEntryMatch.steps n+2)+5)+10)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have key' : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b w).answer = .returned (.ok input) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using key
  have mapped' : (PV_THR2_RunEntryNext.mapReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input w).answer = .returned (.ok mapValue) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using mapped
  have error' : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue w).answer = .returned (.ok value) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using error
  have branch' : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w).answer = .returned (.ok result) := by
    simpa only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] using branch
  have guarded :
    let c := PV_THR2_WrapRunEntryMatch.returned s n f b input mapValue value result
    let source := write c.store ⟨c.frame.activation,5,[]⟩ none
    let post := (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w).world
    let events := PV_THR2_WrapRunEntryMatch.events (PV_THR2_IntrinsicTraceGate.gate handler) s n f b input mapValue value w
    PV_THR2_Execution.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) (PV_THR2_IntrinsicTraceGate.gate handler)
      ((PV_THR2_RunEntryMatch.steps n+2)+5)
      ⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩ =
      match (PV_THR2_EntryDynamic.carrier base b).field result 0 with
      | none => ⟨.undefined (some PV_THR2_RunTlsForward.fieldSite)
          (write source ⟨c.frame.activation,13,[]⟩ none),post,events⟩
      | some actual => ⟨.running ⟨{activation := c.frame.activation,remaining := PV_THR2_F170.live.body.drop 31},
          c.callers,PV_THR2_RunTlsForward.prepared source c.frame.activation actual⟩,post,events⟩ := by
    exact PV_THR2_WrapRunEntryForward.original_forward base ctl _ _ s n f b input mapValue value result w key' mapped' error' branch' variant
  dsimp only at guarded
  rw [field] at guarded
  simp only [PV_THR2_RunEntryReturned.keyReply,PV_THR2_RunEntryNext.mapReply,PV_THR2_RunEntryErrorReply.errorReply,PV_THR2_WrapRunEntryBranchReply.branchReply,PV_THR2_WrapRunEntryMatch.events,PV_THR2_IntrinsicGateShort.one,PV_THR2_IntrinsicGateShort.two] at guarded
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_EntryDynamic.carrier base b) (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler PV_THR2_F0.live [.number n,f] s ((PV_THR2_RunEntryMatch.steps n+2)+5)
    w _ _ _ stack (by rfl) guarded
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    ((PV_THR2_RunEntryMatch.steps n+2)+5) 10 _ _ reached
  · exact PV_THR2_JoinedCertCertOriginalForwardCertificate.run base ctl programs handler s n f b input mapValue value result w stack key mapped error branch variant
  · exact PV_THR2_JoinedCertCertOriginalCallableSyntax.run _ _ programs handler _ _ _ _ _ stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalCallableCertificate
