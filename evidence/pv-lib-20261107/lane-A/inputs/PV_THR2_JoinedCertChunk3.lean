import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk2
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OriginalComparisonExtendedCertificate
import PV_THR2_OriginalF0ToF1Certificate
import PV_THR2_OriginalF1BinaryCertificate
import PV_THR2_OriginalF1PrologueCertificate
import PV_THR2_OriginalWorkerCertificate
import PV_THR2_OriginalWorkerSyntaxCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalF0ToF1Certificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalF0ToF1Certificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n f flag : Data) (w : W) (stack : List Config)
    (literal : base.constant PV_THR2_RunEntryCall.flagDescriptor = some flag) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 14
      ⟨⟨.running (enter PV_THR2_F0.live [n,f] s),w,[]⟩,stack⟩ := by
  exact PV_THR2_JoinedCertDispatchWrapped.append base ctl programs handler 7 7 _ _
    (PV_THR2_OriginalF0ToF1Certificate.boundary base ctl programs handler s n f flag w stack literal)
    (PV_THR2_JoinedCertCertOriginalF0CallCertificate.run base ctl programs handler s n f flag w stack literal)
    (PV_THR2_JoinedCertDispatchSyntax.OriginalF1SyntaxCertificate.run base ctl programs handler _ _ _ w [] stack)
#print axioms run
end PV_THR2_JoinedCertCertOriginalF0ToF1Certificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalF1BinaryCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalF1BinaryCertificate
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body.drop 6},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertFreshSyntaxContinuation.run base ctl programs handler _ w es stack 3
    (PV_THR2_F1.live.body.drop 7) rfl
  · exact PV_THR2_BinaryExecutionShape.step base ctl _ handler _ w _ _ _ _ _ _ rfl rfl rfl
  · intro d world events done waiting remaining
    exact PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler
      PV_THR2_OriginalF1AfterBinarySyntax.instructions (PV_THR2_F1.live.body.drop 9)
      d world events stack done waiting
      (remaining.trans PV_THR2_OriginalF1AfterBinarySyntax.shape)
      PV_THR2_OriginalF1AfterBinarySyntax.quiet
#print axioms run
end PV_THR2_JoinedCertCertOriginalF1BinaryCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalF1PrologueCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalF1PrologueCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n f flag : Data) (w : W) (stack : List Config)
    (literal : base.constant PV_THR2_RunEntryCall.flagDescriptor = some flag) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 17
      ⟨⟨.running (enter PV_THR2_F0.live [n,f] s),w,[]⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchWrapped.append base ctl programs handler 13 4 _ _
    (PV_THR2_OriginalF1PrologueCertificate.boundary base ctl programs handler s n f flag w stack literal)
  · intro k hk
    exact PV_THR2_JoinedCertCertOriginalF0ToF1Certificate.run base ctl programs handler s n f flag w stack literal k (by omega)
  · exact PV_THR2_JoinedCertCertOriginalF1BinaryCertificate.run base ctl programs handler _ _ _ w [] stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalF1PrologueCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalComparisonExtendedCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalComparisonExtendedCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n : Nat) (f : Data) (w : W) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate (PV_THR2_Scalars.carrier base)
      (PV_THR2_Scalars.control ctl) programs handler 22
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_Scalars.carrier base)
    (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
    PV_THR2_F0.live [.number n,f] s 16 w w [] _ stack (by rfl)
    (PV_THR2_RunEntryForce.original_comparison base ctl _ _ s n f w rfl)
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler 16 6 _ _ reached
  · intro k hk
    exact PV_THR2_JoinedCertCertOriginalF1PrologueCertificate.run (PV_THR2_Scalars.carrier base)
      (PV_THR2_Scalars.control ctl) programs handler s (.number n) f (.boolean true) w stack
      (PV_THR2_Scalars.flag base) k (by omega)
  · exact PV_THR2_JoinedCertCertOriginalF1ExtendedCertificate.run _ _ programs handler _ _ _ w [] stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalComparisonExtendedCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWorkerSyntaxCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWorkerSyntaxCertificate
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body.drop 10},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F1.live.body.drop 12) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalWorkerSyntaxCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalWorkerCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalWorkerCertificate
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
      ((16+PV_THR2_RunF1Force.steps (decide (n<32)))+3)
      ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,stack⟩ := by
  have reached := PV_THR2_OriginalPrefixLift.run (PV_THR2_Scalars.carrier base)
    (PV_THR2_Scalars.control ctl)
    (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler
    PV_THR2_F0.live [.number n,f] s (16+PV_THR2_RunF1Force.steps (decide (n<32)))
    w w [] _ stack (by rfl)
    (PV_THR2_RunEntryForce.original_forced base ctl _ _ s n f w rfl)
  apply PV_THR2_JoinedCertDispatchWrapped.append _ _ programs handler
    (16+PV_THR2_RunF1Force.steps (decide (n<32))) 3 _ _ reached
  · intro k hk
    have bound : 16+PV_THR2_RunF1Force.steps (decide (n<32)) ≤ 22 := by
      cases decide (n<32) <;> simp only [PV_THR2_RunF1Force.steps] <;> decide
    exact PV_THR2_JoinedCertCertOriginalComparisonExtendedCertificate.run base ctl programs handler
      s n f w stack k (Nat.lt_of_lt_of_le hk bound)
  · exact PV_THR2_JoinedCertCertOriginalWorkerSyntaxCertificate.run _ _ programs handler _ _ _ w [] stack
#print axioms run
end PV_THR2_JoinedCertCertOriginalWorkerCertificate
