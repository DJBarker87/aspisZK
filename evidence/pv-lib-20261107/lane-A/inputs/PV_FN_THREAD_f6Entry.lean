import PV_THR2_ScopePrologue
import PV_THR2_IntrinsicComposition
import PV_THR2_ScopeCall121
set_option autoImplicit false
namespace PV_FN_THREAD_f6Entry
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- f6's own call entry, arbitrary saved caller suffix, store, world, events
and suspended intrinsic stack. Source Boolean literals are installed by the
existing named carrier. No callee returned case or future-state read. -/
theorem prepare {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : W)
    (events : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) programs handler 16
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,events⟩,stack⟩ =
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 16},parents,
      PV_THR2_ScopePrologue.prepared s a⟩,w,events⟩,stack⟩ := by
  have shape : PV_THR2_F6.live.body =
      [PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15] ++ PV_THR2_F6.live.body.drop 16 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 16 = remaining
  have f : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.1 = some (.boolean false) := rfl
  have t : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.2 = some (.boolean true) := rfl
  simp only [PV_THR2_ScopePrologue.literals,PV_THR2_F6.node6,PV_THR2_F6.node11] at f t
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.advance,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,locate,writeAddress,write,f,t,PV_THR2_ScopePrologue.prepared]

/-- The source guard/storage writes frame every other activation. -/
theorem frame (s : Store Data) (a : Nat) (p : Address) (outside : p.activation ≠ a) :
    (PV_THR2_ScopePrologue.prepared s a).cells p = s.cells p := by
  have neq (i : Nat) : p ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [PV_THR2_ScopePrologue.prepared,write,neq]

/-- The unchanged source121 call is issued at1782, at its actual usize0
argument, before choosing any full reply. No table excludes structured124. -/
theorem request {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : W)
    (events : List E) (stack : List Config) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) programs handler 17
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,events⟩,stack⟩ =
      ⟨⟨.running (PV_THR2_ScopeCall121.pending
        (PV_THR2_ScopePrologue.prepared s a) a parents),w,events⟩,stack⟩ := by
  dsimp only
  rw [show 17 = 16 + 1 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    prepare (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base))
      ctl programs handler s a parents b w events stack]
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step _ _ programs handler _ w events stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl),
    PV_THR2_ScopeCall121.issue base (PV_THR2_Scalars.control ctl)
      programs handler (PV_THR2_ScopePrologue.prepared s a) a parents b w]
  simp only [List.append_nil]

#print axioms prepare
#print axioms frame
#print axioms request
end PV_FN_THREAD_f6Entry
