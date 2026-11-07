import PV_THR2_F164
import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk8
import PV_THR2_JoinedCertChunk9
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OwnUniformSource164Continue268
import PV_THR2_OwnUniformSource164OwnReturn
import PV_THR2_OwnUniformSource164SuffixSyntax
import PV_THR2_Source164Continue268
import PV_THR2_Source164OwnReturn

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionFreshSyntaxContinuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_JoinedCertDispatchTrace
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
      let q := PV_THR2_Execution.step base ctl programs handler c w
      PV_THR2_QuietStatusRange.Range q.status ∧ PV_THR2_QuietInstructionShape.Tail rest q.status)
    (continuation : ∀ (d : Config) (world : W) (events : List E),
      d.frame.completed = none → d.frame.waiting = none → d.frame.remaining = rest →
      Certificate base ctl programs handler n ⟨⟨.running d,world,events⟩,stack⟩) :
    Certificate base ctl programs handler (1+n) ⟨⟨.running c,w,es⟩,stack⟩ := by
  let table := programs
  let q := PV_THR2_Execution.step base ctl table handler c w
  have range : PV_THR2_QuietStatusRange.Range q.status := post.1
  have reached : PV_THR2_IntrinsicState.advance base ctl table handler 1
      ⟨⟨.running c,w,es⟩,stack⟩ = ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
    simp only [PV_THR2_IntrinsicState.advance]
    exact PV_THR2_IntrinsicCompatible.step base ctl table handler c w es stack
      (PV_THR2_IntrinsicCompatible.not_waiting c waiting)
  apply PV_THR2_JoinedCertDispatchTrace.append base ctl programs handler 1 n _ _ reached
  · apply PV_THR2_JoinedCertDispatchTrace.one
    intro d running
    cases running
    exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
  · cases status : q.status with
    | running d =>
      obtain ⟨done,waiting,remaining⟩ := post.2 d status
      exact continuation d q.world (es ++ q.events) done waiting remaining
    | undefined site store =>
      apply PV_THR2_JoinedCertDispatchTrace.gap base ctl programs handler n _ site store
      rfl
    | returned result store =>
      have bad : False := by simpa only [status,PV_THR2_QuietStatusRange.Range] using range
      exact False.elim bad
    | fault f store =>
      have bad : False := by simpa only [status,PV_THR2_QuietStatusRange.Range] using range
      exact False.elim bad
#print axioms run
end PV_THR2_JoinedCertRegionFreshSyntaxContinuation

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionQuietReturnCertificate
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
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler (nodes.length+2)
      ⟨⟨.running c,w,es⟩,stack⟩ := by
  induction nodes generalizing c w es with
  | nil =>
    exact PV_THR2_JoinedCertRegionReturnSyntaxCertificate.run base ctl programs handler c w es stack
      site place rest done waiting remaining
  | cons i nodes ih =>
    have qi := quiet i (List.mem_cons.mpr (Or.inl rfl))
    have shape : c.frame.remaining = .leaf i :: (nodes.map PV_STX2_SliceSyntax.Node.leaf ++
        .leaf (.ret site place) :: rest) := by
      simpa only [List.map_cons,List.cons_append] using remaining
    have post := And.intro
      (PV_THR2_QuietStatusRange.execution base ctl
        programs handler c w i _ done waiting shape qi)
      (PV_THR2_QuietExecutionShape.step base ctl
        programs handler c w i _ done waiting shape qi)
    have certificate := PV_THR2_JoinedCertRegionFreshSyntaxContinuation.run base ctl programs handler c w es stack
      (nodes.length+2) _ waiting post
      (by intro d world events nextDone nextWaiting nextRemaining
          exact ih d world events nextDone nextWaiting nextRemaining
            (by intro j hj; exact quiet j (List.mem_cons_of_mem i hj)))
    have length : 1+(nodes.length+2) = (i::nodes).length+2 := by simp only [List.length_cons]; omega
    rw [length] at certificate
    exact certificate
#print axioms run
end PV_THR2_JoinedCertRegionQuietReturnCertificate

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource164SuffixSyntax
open PV_THR2_OwnUniformSource164SuffixSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 4
      ⟨⟨.running ⟨{activation := a,remaining := [PV_THR2_F164.node3,PV_THR2_F164.node4,PV_THR2_F164.node5] ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertRegionQuietReturnCertificate.run base ctl programs handler instructions _ _ _ _ w es stack rfl rfl rfl
  · intro i h
    simp only [instructions,List.mem_cons] at h
    rcases h with rfl | rfl | bad
    all_goals first | trivial | cases bad
#print axioms run
end PV_THR2_JoinedCertRegionSource164SuffixSyntax

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource164Continue268
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source164Continue268
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a dest : Nat) (parent : Frame) (parents : List Frame)
    (wait : PV_STX2_Native.Waiting Data) (b : Bool) (r : Reply OWNER E Data)
    (es : List E) (stack : List Config)
    (saved : parent.waiting = some wait) (action : wait.action = .child a (.local dest)) :
    let carrier := PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    PV_THR2_JoinedCertDispatchTrace.Certificate carrier ctl programs handler (steps r)
      (PV_THR2_IntrinsicFullLocal.received carrier s a (parent :: parents)
        (PV_THR2_F164.live.body.drop 3) PV_THR2_SourceRawTable.fn268 [] 1 r es stack) := by
  dsimp only
  rcases r with ⟨answer,world,events⟩
  cases answer with
  | pending => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | fault f => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | returned result =>
    cases result with
    | fail e => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | div => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | ok v =>
      simp only [steps]
      rw [PV_THR2_IntrinsicFullLocal.returned]
      exact PV_THR2_JoinedCertRegionSource164SuffixSyntax.run _ ctl programs handler _ a (parent :: parents) [] [] world (es ++ events) stack
#print axioms run
end PV_THR2_JoinedCertRegionSource164Continue268

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource164OwnReturn
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source164OwnReturn
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
      ctl (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback)))
      handler (steps handler s a parents w)
      ⟨⟨.running (PV_THR2_Source15Call164.entered s a parents),w,es⟩,stack⟩ := by
  unfold steps
  apply PV_THR2_JoinedCertDispatchTrace.append _ ctl _ handler ((1+1)+(1+1)) _ _ _
    (PV_THR2_Source164OwnPrefix.run _ ctl fallback handler _ _ _ w es stack)
  · exact PV_THR2_JoinedCertRegionSource164OwnPrefix.run _ ctl fallback handler _ _ _ w es stack
  · exact PV_THR2_JoinedCertRegionSource164Continue268.run base ctl _ handler _ _ 4 _ parents
      (PV_THR2_StaticReply.wait s PV_THR2_Source15Table.fn [] 4) b _ es stack rfl rfl
#print axioms run
end PV_THR2_JoinedCertRegionSource164OwnReturn

set_option autoImplicit false
namespace PV_THR2_JoinedCertRegionQuietCallCertificate
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
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler (nodes.length+2)
      ⟨⟨.running c,w,es⟩,stack⟩ := by
  induction nodes generalizing c w es with
  | nil =>
    exact PV_THR2_JoinedCertRegionStaticSyntaxCertificate.run base ctl programs handler c w es stack
      site kind generics args dest cleanup rest done waiting remaining different
  | cons i nodes ih =>
    have qi := quiet i (List.mem_cons.mpr (Or.inl rfl))
    have shape : c.frame.remaining = .leaf i :: (nodes.map PV_STX2_SliceSyntax.Node.leaf ++
        .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args dest cleanup) :: rest) := by
      simpa only [List.map_cons,List.cons_append] using remaining
    have post := And.intro
      (PV_THR2_QuietStatusRange.execution base ctl
        programs handler c w i _ done waiting shape qi)
      (PV_THR2_QuietExecutionShape.step base ctl
        programs handler c w i _ done waiting shape qi)
    have certificate := PV_THR2_JoinedCertRegionFreshSyntaxContinuation.run base ctl programs handler c w es stack
      (nodes.length+2) _ waiting post
      (by intro d world events nextDone nextWaiting nextRemaining
          exact ih d world events nextDone nextWaiting nextRemaining
            (by intro j hj; exact quiet j (List.mem_cons_of_mem i hj)))
    have length : 1+(nodes.length+2) = (i::nodes).length+2 := by simp only [List.length_cons]; omega
    rw [length] at certificate
    exact certificate
#print axioms run
end PV_THR2_JoinedCertRegionQuietCallCertificate
