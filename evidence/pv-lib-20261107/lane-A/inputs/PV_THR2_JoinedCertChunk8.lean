import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OwnUniformCertificatePrefix
import PV_THR2_OwnUniformSource15Start
import PV_THR2_Source15Start

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionZero
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Empty retained source segment, for every arbitrary child outcome. -/
theorem zero {W E : Type} (C : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H 0 q := by
  intro k hk
  omega
#print axioms zero
end PV_THR2_JoinedCertRegionZero

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionPrefix
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on amended translator acceptance. Hypotheses: the retained
finite operator certificate and a shorter fuel. Restrict its composition;
no instruction, source run or store is re-certified. -/
theorem take {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    {n : Nat} {q : PV_THR2_IntrinsicState.State OWNER E}
    (cert : PV_THR2_JoinedCertDispatchTrace.Certificate C K P H n q)
    (m : Nat) (le : m ≤ n) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H m q := by
  intro k hk
  exact cert k (by omega)
#print axioms take
end PV_THR2_JoinedCertRegionPrefix

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15Start
open PV_THR2_OwnUniformSource15Start
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 4
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertRegionPrefix.take base ctl programs handler
    (n := instructions.length+1) ?_ 4 (by decide)
  apply PV_THR2_JoinedCertDispatchQuiet.quiet_prefix base ctl programs handler
    instructions (PV_THR2_F15.live.body.drop 4) _ w es stack rfl rfl shape quiet
#print axioms run
end PV_THR2_JoinedCertRegionSource15Start

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionStaticSyntaxShape
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem source {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (site : Site) (kind generics : Data)
    (args : List Operand) (dest : Place) (cleanup : List Instruction)
    (rest : List PV_STX2_SliceSyntax.Node)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = .leaf (.call site
      (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args dest cleanup) :: rest)
    (different : (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_Source361PacketChildren.fn58 ∧
      (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_PacketDataTable.fn126 ∧
      (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ⱼ PV_THR2_PacketDataTable.fn222) :
    ∀ d, (PV_STX2_SliceMachine.step base ctl programs handler c w).status = .running d →
      PV_THR2_JoinedCertCertConfiguration.Ordinary d := by
  intro d running
  simp only [PV_STX2_SliceMachine.step,done,waiting,remaining,PV_STX2_SliceMachine.native,
    PV_STX2_Native.step,PV_STX2_SliceMachine.adopt] at running
  cases evaluated : operands base w c.frame.activation args c.store with
  | none => simp only [evaluated,Id.run,pure] at running; cases running
  | some pair =>
    rcases pair with ⟨vs,t⟩
    simp only [evaluated,Id.run,pure,PV_STX2_SliceMachine.Status.running.injEq] at running
    subst d
    exact PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl different.1 different.2.1 different.2.2
#print axioms source
end PV_THR2_JoinedCertRegionStaticSyntaxShape

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionStaticExecutionShape
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem step {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (site : Site) (kind generics : Data)
    (args : List Operand) (dest : Place) (cleanup : List Instruction)
    (rest : List PV_STX2_SliceSyntax.Node)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = .leaf (.call site
      (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args dest cleanup) :: rest)
    (different : (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_Source361PacketChildren.fn58 ∧
      (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_PacketDataTable.fn126 ∧
      (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ⱼ PV_THR2_PacketDataTable.fn222) :
    ∀ d, (PV_THR2_Execution.step base ctl programs handler c w).status = .running d →
      PV_THR2_JoinedCertCertConfiguration.Ordinary d := by
  have inactive : PV_THR2_Dynamic.active c = none := by
    simp only [PV_THR2_Dynamic.active,done,waiting,remaining,PV_THR2_Dynamic.operandOf]
    rfl
  have old := PV_THR2_JoinedCertRegionStaticSyntaxShape.source base ctl programs handler c w site kind generics args dest cleanup rest done waiting remaining different
  have extra := PV_THR2_JoinedCertRegionStaticSyntaxShape.source (PV_THR2_AggregateCompletion.carrier base) ctl programs handler c w site kind generics args dest cleanup rest done waiting remaining different
  simp only [PV_THR2_Execution.step,inactive,PV_THR2_GapCompletion.step]
  generalize result : PV_STX2_SliceMachine.step base ctl programs handler c w = q at *
  cases status : q.status <;> simp only [status]
  · simpa only [status] using old
  · simpa only [status] using old
  · simpa only [status] using old
  · exact extra
#print axioms step
end PV_THR2_JoinedCertRegionStaticExecutionShape

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionStaticSyntaxCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (site : Site) (kind generics : Data) (args : List Operand) (dest : Place)
    (cleanup : List Instruction) (rest : List PV_STX2_SliceSyntax.Node)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = .leaf (.call site
      (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args dest cleanup) :: rest)
    (different : (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_Source361PacketChildren.fn58 ∧
      (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_PacketDataTable.fn126 ∧
      (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ⱼ PV_THR2_PacketDataTable.fn222) :
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
    exact PV_THR2_JoinedCertRegionStaticExecutionShape.step base ctl table handler c w site kind generics args dest cleanup rest done waiting remaining different
#print axioms run
end PV_THR2_JoinedCertRegionStaticSyntaxCertificate
