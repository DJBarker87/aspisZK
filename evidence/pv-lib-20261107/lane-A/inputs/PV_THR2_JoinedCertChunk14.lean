import PV_THR2_BoxPath443DerefFull
import PV_THR2_BoxPath443NewFull
import PV_THR2_BoxPath458Aggregate4
import PV_THR2_BoxPath537Aggregate8
import PV_THR2_BoxPathClosureBoxFull
import PV_THR2_BoxPathEnter443
import PV_THR2_BoxPathEnter458
import PV_THR2_BoxPathEnter537
import PV_THR2_BoxPathUniqueFull
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_IntrinsicChildCall
import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk12
import PV_THR2_JoinedCertChunk8
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OwnUniformBeforeCertificate
import PV_THR2_OwnUniformBoxCertificates
import PV_THR2_OwnUniformSource361Certificates
import PV_THR2_Source15ClosureAggregate
import PV_THR2_Source15SpawnEnter
import PV_THR2_Source166Enter270
import PV_THR2_Source270ArcAggregate
import PV_THR2_Source270ArcStorage
import PV_THR2_Source270Enter361
import PV_THR2_Source270ScopeArcFull
import PV_THR2_Source361Aggregate126
import PV_THR2_Source361Aggregate49
import PV_THR2_Source361Aggregate53
import PV_THR2_Source361Aggregate54
import PV_THR2_Source361Aggregate76
import PV_THR2_Source361AllocationFull
import PV_THR2_Source361CloneFull
import PV_THR2_Source361FirstAggregate
import PV_THR2_Source361Full23
import PV_THR2_Source361Full27
import PV_THR2_Source361Full34
import PV_THR2_Source361Full50
import PV_THR2_Source361Full58
import PV_THR2_Source361Full63
import PV_THR2_Source361Full70
import PV_THR2_Source361Full81
import PV_THR2_Source361HookBranch
import PV_THR2_Source361HookFalseFull
import PV_THR2_Source361HookTrueFull
import PV_THR2_Source361ScopeMatch
import PV_THR2_Source361ScopeSomeCountFull
import PV_THR2_Source361ScopeSomeDerefFull

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionFrontierCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_THR2_IntrinsicFrameChain
/-- Conditional on owner acceptance of amended translator. Hypothesis: the
existing finite certificate on the source-selected frontier. Lift ONLY the
certificate through the original segment's zero-fuel cases; no source run is
re-proved and no endpoint restriction is introduced. -/
theorem selected {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (nodes : List PV_STX2_SliceSyntax.Node) (cost : Config → OWNER → Nat)
    (certificate : ∀ c w es stack, PV_THR2_IntrinsicAtContinuation.Ready nodes c →
      PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (cost c w)
        ⟨⟨.running c,w,es⟩,stack⟩)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
      (PV_THR2_IntrinsicAtContinuation.steps nodes cost q) q := by
  classical
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases status with
  | running c =>
    by_cases ready : PV_THR2_IntrinsicAtContinuation.Ready nodes c
    · simpa only [PV_THR2_IntrinsicAtContinuation.steps,if_pos ready] using certificate c w es stack ready
    · simp only [PV_THR2_IntrinsicAtContinuation.steps,if_neg ready]
      exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | returned r s => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | fault f s => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | undefined site s => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
/-- Conditional on owner acceptance of amended translator. Hypotheses: the
existing named shape and generated neutral chain certificates. Connect those
certificates to the actual total source segment used by original_scope_invoke,
including its missing-operand and unrelated-frontier cases. -/
theorem chain {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (chain : Chain) (nodes rest : List PV_STX2_SliceSyntax.Node)
    (shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ rest = nodes)
    (neutral : PV_THR2_JoinedCertRegionChainCertificate.Neutral chain)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
      (PV_THR2_IntrinsicAtContinuation.steps nodes
        (fun c w => steps C c.frame.activation w chain c.store) q) q := by
  apply selected
  intro c w es stack ready
  rw [PV_THR2_IntrinsicAtContinuation.frame c ready]
  dsimp only
  rw [← shape]
  exact PV_THR2_JoinedCertRegionChainCertificate.run C K P H chain c.store c.frame.activation
    c.callers c.frame.loops rest w es stack neutral
#print axioms selected
#print axioms chain
end PV_THR2_JoinedCertRegionFrontierCertificate

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionFrontierCertificates
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361Chain24To27 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Chain24To27.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361Chain24To27.chain _ _
    PV_THR2_Source361Chain24To27.shape PV_THR2_OwnUniformSource361Certificates.Source361Chain24To27 q
#print axioms Source361Chain24To27
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361Chain28To34 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Chain28To34.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361Chain28To34.chain _ _
    PV_THR2_Source361Chain28To34.shape PV_THR2_OwnUniformSource361Certificates.Source361Chain28To34 q
#print axioms Source361Chain28To34
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361Chain35To40 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Chain35To40.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361Chain35To40.chain _ _
    PV_THR2_Source361Chain35To40.shape PV_THR2_OwnUniformSource361Certificates.Source361Chain35To40 q
#print axioms Source361Chain35To40
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361Chain41To49 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Chain41To49.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361Chain41To49.chain _ _
    PV_THR2_Source361Chain41To49.shape PV_THR2_OwnUniformSource361Certificates.Source361Chain41To49 q
#print axioms Source361Chain41To49
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361Chain51To53 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Chain51To53.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361Chain51To53.chain _ _
    PV_THR2_Source361Chain51To53.shape PV_THR2_OwnUniformSource361Certificates.Source361Chain51To53 q
#print axioms Source361Chain51To53
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361Chain55To58 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Chain55To58.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361Chain55To58.chain _ _
    PV_THR2_Source361Chain55To58.shape PV_THR2_OwnUniformSource361Certificates.Source361Chain55To58 q
#print axioms Source361Chain55To58
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361HookFalsePrefix {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361HookFalsePrefix.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361HookFalsePrefix.chain _ _
    PV_THR2_Source361HookFalsePrefix.shape PV_THR2_OwnUniformSource361Certificates.Source361HookFalsePrefix q
#print axioms Source361HookFalsePrefix
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361HookFalseSuffix {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361HookFalseSuffix.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361HookFalseSuffix.chain _ _
    PV_THR2_Source361HookFalseSuffix.shape PV_THR2_OwnUniformSource361Certificates.Source361HookFalseSuffix q
#print axioms Source361HookFalseSuffix
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361HookTrueSuffix {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361HookTrueSuffix.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361HookTrueSuffix.chain _ _
    PV_THR2_Source361HookTrueSuffix.shape PV_THR2_OwnUniformSource361Certificates.Source361HookTrueSuffix q
#print axioms Source361HookTrueSuffix
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate join for the already proved original source segment.
Every symbolic store, missing binding and unrelated frontier is retained. -/
theorem Source361Prologue {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Prologue.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source361Prologue.chain _ _
    PV_THR2_Source361Prologue.shape PV_THR2_OwnUniformSource361Certificates.Source361Prologue q
#print axioms Source361Prologue
end PV_THR2_JoinedCertRegionFrontierCertificates

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionChildCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypothesis: the
named call's aggregate-completion operand stability. Trace certificate for the
already proved child composition, with every missing operand and FULL reply.
The call and its waiting frame are neutral by instruction shape. -/
theorem run {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : Site) (kind generics : Data)
    (args : List Operand) (dest : Nat) (w : OWNER) (es : List E) (stack : List Config)
    (stable : operands (PV_THR2_AggregateCompletion.carrier C) w a args s = operands C w a args s)
    (different : (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_Source361PacketChildren.fn58 ∧ (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_PacketDataTable.fn126 ∧ (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ⱼ PV_THR2_PacketDataTable.fn222) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
      (PV_THR2_IntrinsicChildCall.steps C s a args w)
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.call site
        (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  unfold PV_THR2_IntrinsicChildCall.steps
  apply PV_THR2_JoinedCertDispatchTrace.append C K P H 1 _ _ _
    (PV_THR2_IntrinsicFrameCall.run C K P H s a parents loops rest site kind generics args dest w es stack stable)
  · apply PV_THR2_JoinedCertDispatchTrace.one
    intro c eq
    cases eq
    exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
  · unfold PV_THR2_IntrinsicFrameCall.after
    cases h : operands C w a args s with
    | none => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | some pair =>
      rcases pair with ⟨vs,t⟩
      apply PV_THR2_JoinedCertDispatchTrace.one
      intro c eq
      cases eq
      apply PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl
      · exact different.1
      · exact different.2.1
      · exact different.2.2
#print axioms run
end PV_THR2_JoinedCertRegionChildCertificate

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionChildFrontiers
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named FULL child composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source270ScopeArcFull {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source270ScopeArcFull.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source270ScopeArcFull.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F270.node27 :: PV_THR2_F270.live.body.drop 28,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source270ScopeArcFull.source.1
    PV_THR2_Source270ScopeArcFull.source.2.1 PV_THR2_Source270ScopeArcFull.source.2.2.1 PV_THR2_Source270ScopeArcFull.source.2.2.2.1 PV_THR2_Source270ScopeArcFull.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source270ScopeArcFull
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named FULL child composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source361Full23 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Full23.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source361Full23.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node23 :: PV_THR2_F361.live.body.drop 24,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source361Full23.source.1
    PV_THR2_Source361Full23.source.2.1 PV_THR2_Source361Full23.source.2.2.1 PV_THR2_Source361Full23.source.2.2.2.1 PV_THR2_Source361Full23.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source361Full23
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named FULL child composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source361Full27 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Full27.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source361Full27.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node27 :: PV_THR2_F361.live.body.drop 28,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source361Full27.source.1
    PV_THR2_Source361Full27.source.2.1 PV_THR2_Source361Full27.source.2.2.1 PV_THR2_Source361Full27.source.2.2.2.1 PV_THR2_Source361Full27.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source361Full27
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named FULL child composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source361Full34 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Full34.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source361Full34.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node34 :: PV_THR2_F361.live.body.drop 35,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source361Full34.source.1
    PV_THR2_Source361Full34.source.2.1 PV_THR2_Source361Full34.source.2.2.1 PV_THR2_Source361Full34.source.2.2.2.1 PV_THR2_Source361Full34.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source361Full34
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named FULL child composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source361HookTrueFull {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361HookTrueFull.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source361HookTrueFull.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node40 :: (PV_THR2_F361.block42.drop 1 ++ PV_THR2_F361.live.body.drop 41),loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source361HookTrueFull.source.1
    PV_THR2_Source361HookTrueFull.source.2.1 PV_THR2_Source361HookTrueFull.source.2.2.1 PV_THR2_Source361HookTrueFull.source.2.2.2.1 PV_THR2_Source361HookTrueFull.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source361HookTrueFull
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named FULL child composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source361HookFalseFull {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361HookFalseFull.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source361HookFalseFull.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node47 :: (PV_THR2_F361.block51.drop 5 ++ PV_THR2_F361.live.body.drop 41),loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source361HookFalseFull.source.1
    PV_THR2_Source361HookFalseFull.source.2.1 PV_THR2_Source361HookFalseFull.source.2.2.1 PV_THR2_Source361HookFalseFull.source.2.2.2.1 PV_THR2_Source361HookFalseFull.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source361HookFalseFull
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named FULL child composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source361Full50 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Full50.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source361Full50.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node62 :: PV_THR2_F361.live.body.drop 51,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source361Full50.source.1
    PV_THR2_Source361Full50.source.2.1 PV_THR2_Source361Full50.source.2.2.1 PV_THR2_Source361Full50.source.2.2.2.1 PV_THR2_Source361Full50.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source361Full50
end PV_THR2_JoinedCertRegionChildFrontiers

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionEntryFrontiers
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named structured entry composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source15SpawnEnter {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source15SpawnEnter.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source15SpawnEnter.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node35 :: PV_THR2_F15.block47.drop 21,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source15SpawnEnter.source.1
    PV_THR2_Source15SpawnEnter.source.2.1 PV_THR2_Source15SpawnEnter.source.2.2.1 PV_THR2_Source15SpawnEnter.source.2.2.2.1 PV_THR2_Source15SpawnEnter.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source15SpawnEnter
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named structured entry composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source166Enter270 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source166Enter270.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source166Enter270.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F166.node12 :: PV_THR2_F166.live.body.drop 13,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source166Enter270.source.1
    PV_THR2_Source166Enter270.source.2.1 PV_THR2_Source166Enter270.source.2.2.1 PV_THR2_Source166Enter270.source.2.2.2.1 PV_THR2_Source166Enter270.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source166Enter270
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the original named structured entry composition by syntax.
Actual argument failures, all replies and their backend/events stay symbolic. -/
theorem Source270Enter361 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source270Enter361.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
    (PV_THR2_IntrinsicChildCall.steps C s a PV_THR2_Source270Enter361.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F270.node35 :: PV_THR2_F270.live.body.drop 36,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops _ PV_THR2_Source270Enter361.source.1
    PV_THR2_Source270Enter361.source.2.1 PV_THR2_Source270Enter361.source.2.2.1 PV_THR2_Source270Enter361.source.2.2.2.1 PV_THR2_Source270Enter361.source.2.2.2.2 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source270Enter361
end PV_THR2_JoinedCertRegionEntryFrontiers

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionOneFrontiers
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated trace certificate using the existing segment's actual next syntax.
Branch and match successors, stores and all failures stay entirely symbolic. -/
theorem Source15ClosureAggregate {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source15ClosureAggregate.steps q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node34 :: PV_THR2_F15.block47.drop 20,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c eq
  cases eq
  exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms Source15ClosureAggregate
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated trace certificate using the existing segment's actual next syntax.
Branch and match successors, stores and all failures stay entirely symbolic. -/
theorem Source270ArcStorage {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source270ArcStorage.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F270.node28 :: PV_THR2_F270.live.body.drop 29,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c eq
  cases eq
  exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms Source270ArcStorage
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated trace certificate using the existing segment's actual next syntax.
Branch and match successors, stores and all failures stay entirely symbolic. -/
theorem Source270ArcAggregate {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source270ArcAggregate.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F270.node29 :: PV_THR2_F270.live.body.drop 30,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c eq
  cases eq
  exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms Source270ArcAggregate
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated trace certificate using the existing segment's actual next syntax.
Branch and match successors, stores and all failures stay entirely symbolic. -/
theorem Source361FirstAggregate {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361FirstAggregate.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node22 :: PV_THR2_F361.live.body.drop 23,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c eq
  cases eq
  exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms Source361FirstAggregate
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated trace certificate using the existing segment's actual next syntax.
Branch and match successors, stores and all failures stay entirely symbolic. -/
theorem Source361HookBranch {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361HookBranch.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node52 :: PV_THR2_F361.live.body.drop 41,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c eq
  cases eq
  exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms Source361HookBranch
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated trace certificate using the existing segment's actual next syntax.
Branch and match successors, stores and all failures stay entirely symbolic. -/
theorem Source361Aggregate49 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Aggregate49.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node61 :: PV_THR2_F361.live.body.drop 50,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c eq
  cases eq
  exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms Source361Aggregate49
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated trace certificate using the existing segment's actual next syntax.
Branch and match successors, stores and all failures stay entirely symbolic. -/
theorem Source361Aggregate53 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Aggregate53.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node65 :: PV_THR2_F361.live.body.drop 54,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c eq
  cases eq
  exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms Source361Aggregate53
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated trace certificate using the existing segment's actual next syntax.
Branch and match successors, stores and all failures stay entirely symbolic. -/
theorem Source361Aggregate54 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source361Aggregate54.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node66 :: PV_THR2_F361.live.body.drop 55,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_THR2_JoinedCertDispatchTrace.one
  intro c eq
  cases eq
  exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
#print axioms Source361Aggregate54
end PV_THR2_JoinedCertRegionOneFrontiers
