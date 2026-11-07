import PV_THR2_BranchExecutionShape
import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_Original219CapturesSyntax
import PV_THR2_OriginalF0CallCertificate
import PV_THR2_OriginalF0SyntaxCertificate
import PV_THR2_OriginalF170EarlySyntax
import PV_THR2_OriginalF17EarlySyntax
import PV_THR2_OriginalF1AfterBinarySyntax
import PV_THR2_OriginalF1ExtendedCertificate
import PV_THR2_OriginalF1SyntaxCertificate
import PV_THR2_OriginalF2EarlySyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertDispatchSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
namespace Original219CapturesSyntax
open PV_THR2_Original219CapturesSyntax
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Consume the retained source shape and Quiet lemmas BY NAME. Only exact Packet
descriptor independence is new; no original prefix execution is re-proved. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 11
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 6},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler instructions
    (PV_THR2_F219.live.body.drop 16) _ w es stack rfl rfl shape quiet
#print axioms run
end Original219CapturesSyntax
namespace OriginalF0SyntaxCertificate
open PV_THR2_OriginalF0SyntaxCertificate
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Consume the retained source shape and Quiet lemmas BY NAME. Only exact Packet
descriptor independence is new; no original prefix execution is re-proved. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 6
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F0.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F0.live.body.drop 5) _ w es stack rfl rfl shape quiet
#print axioms run
end OriginalF0SyntaxCertificate
namespace OriginalF170EarlySyntax
open PV_THR2_OriginalF170EarlySyntax
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Consume the retained source shape and Quiet lemmas BY NAME. Only exact Packet
descriptor independence is new; no original prefix execution is re-proved. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 14
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler instructions
    (PV_THR2_F170.live.body.drop 13) _ w es stack rfl rfl shape quiet
#print axioms run
end OriginalF170EarlySyntax
namespace OriginalF1AfterBinarySyntax
open PV_THR2_OriginalF1AfterBinarySyntax
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Consume the retained source shape and Quiet lemmas BY NAME. Only exact Packet
descriptor independence is new; no original prefix execution is re-proved. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body.drop 7},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F1.live.body.drop 9) _ w es stack rfl rfl shape quiet
#print axioms run
end OriginalF1AfterBinarySyntax
namespace OriginalF1SyntaxCertificate
open PV_THR2_OriginalF1SyntaxCertificate
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Consume the retained source shape and Quiet lemmas BY NAME. Only exact Packet
descriptor independence is new; no original prefix execution is re-proved. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 7
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F1.live.body.drop 6) _ w es stack rfl rfl shape quiet
#print axioms run
end OriginalF1SyntaxCertificate
end PV_THR2_JoinedCertDispatchSyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalF17EarlySyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalF17EarlySyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F17.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F17.live.body.drop 7) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalF17EarlySyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalF2EarlySyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalF2EarlySyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F2.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _
    (PV_THR2_F2.live.body.drop 6) _ w es stack rfl rfl shape quiet
  exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalF2EarlySyntax

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertBranchSyntaxContinuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_JoinedCertDispatchWrapped
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (n : Nat) (yes no rest : List PV_STX2_SliceSyntax.Node)
    (waiting : c.frame.waiting = none)
    (post :
      let q := PV_THR2_Execution.step base ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler c w
      PV_THR2_QuietStatusRange.Range q.status ∧ PV_THR2_BranchSyntaxShape.Tail yes no rest q.status)
    (continuation : ∀ (d : Config) (world : W) (events : List E),
      d.frame.completed = none → d.frame.waiting = none → (d.frame.remaining = yes ++ rest ∨ d.frame.remaining = no ++ rest) →
      Certificate base ctl programs handler n ⟨⟨.running d,world,events⟩,stack⟩) :
    Certificate base ctl programs handler (1+n) ⟨⟨.running c,w,es⟩,stack⟩ := by
  let table := PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)
  let q := PV_THR2_Execution.step base ctl table handler c w
  have range : PV_THR2_QuietStatusRange.Range q.status := post.1
  have reached : PV_THR2_IntrinsicState.advance base ctl table handler 1
      ⟨⟨.running c,w,es⟩,stack⟩ = ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
    simp only [PV_THR2_IntrinsicState.advance]
    exact PV_THR2_IntrinsicCompatible.step base ctl table handler c w es stack
      (PV_THR2_IntrinsicCompatible.not_waiting c waiting)
  apply PV_THR2_JoinedCertDispatchWrapped.append base ctl programs handler 1 n _ _ reached
  · apply PV_THR2_JoinedCertDispatchWrapped.one
    intro d running
    cases running
    exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
  · cases status : q.status with
    | running d =>
      obtain ⟨done,waiting,remaining⟩ := post.2 d status
      exact continuation d q.world (es ++ q.events) done waiting remaining
    | undefined site store =>
      apply PV_THR2_JoinedCertDispatchWrapped.gap base ctl programs handler n _ site store
      rfl
    | returned result store =>
      have bad : False := by simpa only [status,PV_THR2_QuietStatusRange.Range] using range
      exact False.elim bad
    | fault f store =>
      have bad : False := by simpa only [status,PV_THR2_QuietStatusRange.Range] using range
      exact False.elim bad
#print axioms run
end PV_THR2_JoinedCertCertBranchSyntaxContinuation

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalF1ExtendedCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalF1ExtendedCertificate
open PV_THR2_OriginalF1ExtendedSyntax
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
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F1.live.body.drop 9},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertCertBranchSyntaxContinuation.run base ctl programs handler _ w es stack 5
    PV_THR2_F1.block41 PV_THR2_F1.block44 (PV_THR2_F1.live.body.drop 10) rfl
  · exact PV_THR2_BranchExecutionShape.step base ctl _ handler _ w _ _ _ _ _ rfl rfl rfl
  · intro d world events done waiting remaining
    rcases remaining with yes | no
    · apply PV_THR2_JoinedCertDispatchWrapped.quiet_prefix base ctl programs handler
        yesInstructions (PV_THR2_F1.block41.drop 4 ++ PV_THR2_F1.live.body.drop 10)
        d world events stack done waiting _ yesQuiet
      exact yes.trans ((congrArg (fun xs => xs ++ PV_THR2_F1.live.body.drop 10) yesShape).trans (List.append_assoc _ _ _))
    · apply PV_THR2_JoinedCertCertQuietCallCertificate.run base ctl programs handler
        noInstructions _ _ _ _ _ _ (PV_THR2_F1.live.body.drop 12)
        d world events stack done waiting (no.trans noShape) noQuiet
      exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)
#print axioms run
end PV_THR2_JoinedCertCertOriginalF1ExtendedCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertOriginalF0CallCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_OriginalF0CallCertificate
/-- Conditional on amended-translator acceptance. Internal exclusion certificate
for the UNCHANGED original composition. Source boundaries, instruction shapes
and Quiet facts are reused BY NAME; no source execution is re-proved and no
resolver is attached at an intermediate cut. Not a closure hypothesis. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (n f flag : Data) (w : W) (stack : List Config)
    (literal : base.constant PV_THR2_RunEntryCall.flagDescriptor = some flag) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 7
      ⟨⟨.running (enter PV_THR2_F0.live [n,f] s),w,[]⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchWrapped.append base ctl programs handler 6 1 _ _
    (PV_THR2_OriginalF0CallCertificate.boundary base ctl programs handler s n f flag w stack literal)
  · exact PV_THR2_JoinedCertDispatchSyntax.OriginalF0SyntaxCertificate.run base ctl programs handler _ _ _ w [] stack
  · apply PV_THR2_JoinedCertDispatchWrapped.one
    intro c running
    cases running
    exact PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl PV_THR2_JoinedCertDispatchIds.call16.1 PV_THR2_JoinedCertDispatchIds.call16.2.1 PV_THR2_JoinedCertDispatchIds.call16.2.2
#print axioms run
end PV_THR2_JoinedCertCertOriginalF0CallCertificate
