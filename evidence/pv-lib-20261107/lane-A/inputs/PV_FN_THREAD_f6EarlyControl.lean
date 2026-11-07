import PV_FN_THREAD_f6Constructors
import PV_FN_THREAD_f6Interfaces
set_option autoImplicit false
namespace PV_FN_THREAD_f6EarlyControl
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

theorem activation4 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) (n : Nat) (lower : 0 ≤ n) (bound : n ≤ 4) :
    ∃ c, (PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) P H n
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,
        w,es⟩,stack⟩).current.status = .running c ∧ c.frame.activation = a := by
  have shape : PV_THR2_F6.live.body =
    [PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15] ++ PV_THR2_F6.live.body.drop 16 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 16 = remaining
  have f : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.1 = some (.boolean false) := rfl
  have t : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.2 = some (.boolean true) := rfl
  simp only [PV_THR2_ScopePrologue.literals,PV_THR2_F6.node6,PV_THR2_F6.node11] at f t
  have options : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases options with h0 | h1 | h2 | h3 | h4
  all_goals subst n
  all_goals simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,locate,writeAddress,write,f,t]


theorem activation8 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) (n : Nat) (lower : 5 ≤ n) (bound : n ≤ 8) :
    ∃ c, (PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) P H n
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,
        w,es⟩,stack⟩).current.status = .running c ∧ c.frame.activation = a := by
  have shape : PV_THR2_F6.live.body =
    [PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15] ++ PV_THR2_F6.live.body.drop 16 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 16 = remaining
  have f : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.1 = some (.boolean false) := rfl
  have t : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.2 = some (.boolean true) := rfl
  simp only [PV_THR2_ScopePrologue.literals,PV_THR2_F6.node6,PV_THR2_F6.node11] at f t
  have options : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases options with h5 | h6 | h7 | h8
  all_goals subst n
  all_goals simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,locate,writeAddress,write,f,t]


theorem activation12 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) (n : Nat) (lower : 9 ≤ n) (bound : n ≤ 12) :
    ∃ c, (PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) P H n
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,
        w,es⟩,stack⟩).current.status = .running c ∧ c.frame.activation = a := by
  have shape : PV_THR2_F6.live.body =
    [PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15] ++ PV_THR2_F6.live.body.drop 16 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 16 = remaining
  have f : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.1 = some (.boolean false) := rfl
  have t : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.2 = some (.boolean true) := rfl
  simp only [PV_THR2_ScopePrologue.literals,PV_THR2_F6.node6,PV_THR2_F6.node11] at f t
  have options : n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 := by omega
  rcases options with h9 | h10 | h11 | h12
  all_goals subst n
  all_goals simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,locate,writeAddress,write,f,t]


theorem activation15 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) (n : Nat) (lower : 13 ≤ n) (bound : n ≤ 15) :
    ∃ c, (PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) P H n
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,
        w,es⟩,stack⟩).current.status = .running c ∧ c.frame.activation = a := by
  have shape : PV_THR2_F6.live.body =
    [PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15] ++ PV_THR2_F6.live.body.drop 16 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 16 = remaining
  have f : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.1 = some (.boolean false) := rfl
  have t : (PV_THR2_EntryDynamic.carrier base b).constant PV_THR2_ScopePrologue.literals.2 = some (.boolean true) := rfl
  simp only [PV_THR2_ScopePrologue.literals,PV_THR2_F6.node6,PV_THR2_F6.node11] at f t
  have options : n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases options with h13 | h14 | h15
  all_goals subst n
  all_goals simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node0,PV_THR2_F6.node1,PV_THR2_F6.node2,PV_THR2_F6.node3,PV_THR2_F6.node4,PV_THR2_F6.node5,PV_THR2_F6.node6,PV_THR2_F6.node7,PV_THR2_F6.node8,PV_THR2_F6.node9,PV_THR2_F6.node10,PV_THR2_F6.node11,PV_THR2_F6.node12,PV_THR2_F6.node13,PV_THR2_F6.node14,PV_THR2_F6.node15,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,locate,writeAddress,write,f,t]

theorem activation {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) (n : Nat) (bound : n ≤ 16) :
    ∃ c, (PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b)
      (PV_THR2_Scalars.control ctl) P H n
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,
        w,es⟩,stack⟩).current.status = .running c ∧ c.frame.activation = a := by
  by_cases h4 : n ≤ 4
  · exact activation4 base ctl P H s a parents b w es stack n (Nat.zero_le _) h4
  by_cases h8 : n ≤ 8
  · exact activation8 base ctl P H s a parents b w es stack n (by omega) h8
  by_cases h12 : n ≤ 12
  · exact activation12 base ctl P H s a parents b w es stack n (by omega) h12
  by_cases h15 : n ≤ 15
  · exact activation15 base ctl P H s a parents b w es stack n (by omega) h15
  have equal : n = 16 := by omega
  subst n
  rw [PV_FN_THREAD_f6Entry.prepare base ctl P H s a parents b w es stack]
  exact ⟨_,rfl,rfl⟩

#print axioms activation4
#print axioms activation8
#print axioms activation12
#print axioms activation15
#print axioms activation
end PV_FN_THREAD_f6EarlyControl
