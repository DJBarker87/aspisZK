import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertStaticSyntaxShape
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
end PV_THR2_JoinedCertCertStaticSyntaxShape

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertStaticExecutionShape
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
  have old := PV_THR2_JoinedCertCertStaticSyntaxShape.source base ctl programs handler c w site kind generics args dest cleanup rest done waiting remaining different
  have extra := PV_THR2_JoinedCertCertStaticSyntaxShape.source (PV_THR2_AggregateCompletion.carrier base) ctl programs handler c w site kind generics args dest cleanup rest done waiting remaining different
  simp only [PV_THR2_Execution.step,inactive,PV_THR2_GapCompletion.step]
  generalize result : PV_STX2_SliceMachine.step base ctl programs handler c w = q at *
  cases status : q.status <;> simp only [status]
  · simpa only [status] using old
  · simpa only [status] using old
  · simpa only [status] using old
  · exact extra
#print axioms step
end PV_THR2_JoinedCertCertStaticExecutionShape

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertStaticSyntaxCertificate
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
    exact PV_THR2_JoinedCertCertStaticExecutionShape.step base ctl table handler c w site kind generics args dest cleanup rest done waiting remaining different
#print axioms run
end PV_THR2_JoinedCertCertStaticSyntaxCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertFreshSyntaxContinuation
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
    (n : Nat) (rest : List PV_STX2_SliceSyntax.Node)
    (waiting : c.frame.waiting = none)
    (post :
      let q := PV_THR2_Execution.step base ctl (PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)) handler c w
      PV_THR2_QuietStatusRange.Range q.status ∧ PV_THR2_QuietInstructionShape.Tail rest q.status)
    (continuation : ∀ (d : Config) (world : W) (events : List E),
      d.frame.completed = none → d.frame.waiting = none → d.frame.remaining = rest →
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
end PV_THR2_JoinedCertCertFreshSyntaxContinuation

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertQuietCallCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (nodes : List Instruction) (site : Site) (kind generics : Data)
    (args : List Operand) (dest : Place) (cleanup : List Instruction)
    (rest : List PV_STX2_SliceSyntax.Node)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = nodes.map PV_STX2_SliceSyntax.Node.leaf ++
      .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args dest cleanup) :: rest)
    (quiet : ∀ i, i ∈ nodes → PV_THR2_QuietInstructionShape.Quiet i)
    (different : (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_Source361PacketChildren.fn58 ∧
      (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ PV_THR2_PacketDataTable.fn126 ∧
      (.object [("Regular",.object [("kind",kind),("generics",generics)])] : Data) ≠ⱼ PV_THR2_PacketDataTable.fn222) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler (nodes.length+2)
      ⟨⟨.running c,w,es⟩,stack⟩ := by
  induction nodes generalizing c w es with
  | nil =>
    exact PV_THR2_JoinedCertCertStaticSyntaxCertificate.run base ctl programs handler c w es stack
      site kind generics args dest cleanup rest done waiting remaining different
  | cons i nodes ih =>
    have qi := quiet i (List.mem_cons.mpr (Or.inl rfl))
    have shape : c.frame.remaining = .leaf i :: (nodes.map PV_STX2_SliceSyntax.Node.leaf ++
        .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args dest cleanup) :: rest) := by
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
end PV_THR2_JoinedCertCertQuietCallCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertDispatchIds
open PV_STX2_Syntax
/-- Internal syntax test only. Different regular function identities imply
inequality of the three exact retained Packet descriptors; payloads, addresses
and post-worlds are not inspected. Equal identities require exact metadata. -/
theorem by_id (fn : Data)
    (not124 : PV_THR2_OffPath.functionId fn ≠ some 124)
    (not126 : PV_THR2_OffPath.functionId fn ≠ some 126)
    (not222 : PV_THR2_JoinedCertDescriptor.IdSafe fn) :
    fn ≠ PV_THR2_Source361PacketChildren.fn58 ∧
    fn ≠ PV_THR2_PacketDataTable.fn126 ∧ fn ≠ⱼ PV_THR2_PacketDataTable.fn222 := by
  refine ⟨?_,?_,?_,not222.2⟩
  · intro h; exact not124 (congrArg PV_THR2_OffPath.functionId h)
  · intro h; exact not126 (congrArg PV_THR2_OffPath.functionId h)
  · intro h; exact not222.1 (congrArg PV_THR2_OffPath.functionId h)
/-- Conditional on amended-translator acceptance. Exact emitted call16 uses
function1, so it is independent of all three Packet overrides. -/
theorem call16 : PV_THR2_RunEntryCall.callee ≠ PV_THR2_Source361PacketChildren.fn58 ∧
    PV_THR2_RunEntryCall.callee ≠ PV_THR2_PacketDataTable.fn126 ∧
    PV_THR2_RunEntryCall.callee ≠ⱼ PV_THR2_PacketDataTable.fn222 :=
  by_id _ (by decide) (by decide) (by decide)
#print axioms by_id
#print axioms call16
end PV_THR2_JoinedCertDispatchIds
