import PV_FN_THREAD_f6ScopeData
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ArcRequest
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6ConstructorRun PV_FN_THREAD_f6Constructors

/-- Execute the actual three StorageDead operations and source1916 move,
retaining the intrinsic caller stack and the precise shared store. -/
theorem issue {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (v : Data)
    (w : W) (es : List E) (stack : List Config)
    (cell : s.cells ⟨a,4,[]⟩ = some v) :
    PV_THR2_IntrinsicState.advance B K P H 4
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 22},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_THR2_ScopeArcCall.pending s a parents v),w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.live.body.drop 22 =
    [PV_THR2_F6.node22,PV_THR2_F6.node23,PV_THR2_F6.node24,PV_THR2_F6.node25] ++ PV_THR2_F6.live.body.drop 26 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 26 = remaining
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F6.node22,PV_THR2_F6.node23,PV_THR2_F6.node24,PV_THR2_F6.node25,
    native,adopt,PV_STX2_Native.step,operands,operand,PV_STX2_Store.read,
    locate,writeAddress,write,cell,PV_THR2_ScopeArcCall.before,
    PV_THR2_ScopeArcCall.pending,PV_THR2_StaticCall.pending,
    PV_THR2_StaticCall.issued,PV_THR2_ScopeArcCall.fn,PV_THR2_ScopeChildren.descriptor,tail]
  rfl

/-- Derive the ScopeData aggregate and request1916 from the actual constructor
stores. The entry activation bound is the usual call-entry validity clause. -/
theorem after_constructors {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (x y z : Data) (w : W) (es : List E) (stack : List Config)
    (live : a < s.nextActivation) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) P H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 21},parents,
        third (second (first s a x) a y) a z⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6ScopeData.pending s a parents x y z),w,es⟩,stack⟩ := by
  dsimp only
  have cs := PV_FN_THREAD_f6ScopeData.cells s a x y z live
  rw [show 5 = 1 + 4 from rfl,PV_THR2_IntrinsicComposition.advance_add]
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step _ _ P H _ w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl),
    PV_THR2_ScopeData.aggregate _ _ P H _ a parents b w x y z cs.1 cs.2.1 cs.2.2]
  simp only [List.append_nil]
  exact issue (PV_THR2_EntryDynamic.carrier
    (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b)
    (PV_THR2_Scalars.control ctl) P H
    (PV_THR2_ScopeData.prepared (third (second (first s a x) a y) a z) a x y z)
    a parents (PV_THR2_ScopeData.value x y z) w es stack (by
    simp [PV_THR2_ScopeData.prepared,write])

/-- f6 OWN CALL ENTRY to its actual ScopeData Arc request. Only returned cases
of the three LEAF children occur as reply premises. This is a prefix, not a
complete f6 contract: W2's124 contract at this instantiation remains open. -/
theorem from_entry {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (counter thread panicked : Data) (w : W) (es : List E) (stack : List Config)
    (live : a < s.nextActivation)
    (leaf121 : (H (.child PV_THR2_ScopeCall121.fn s.nextActivation [.number 0]) w).answer = .returned (.ok counter))
    (leaf122 : (H (.child PV_THR2_ScopeCall122.fn (first s a counter).nextActivation [])
      (H (.child PV_THR2_ScopeCall121.fn s.nextActivation [.number 0]) w).world).answer = .returned (.ok thread))
    (leaf123 : (H (.child PV_THR2_ScopeCall123.fn (second (first s a counter) a thread).nextActivation [.boolean false])
      (H (.child PV_THR2_ScopeCall122.fn (first s a counter).nextActivation [])
        (H (.child PV_THR2_ScopeCall121.fn s.nextActivation [.number 0]) w).world).world).answer = .returned (.ok panicked)) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    let r1 := H (.child PV_THR2_ScopeCall121.fn s.nextActivation [.number 0]) w
    let r2 := H (.child PV_THR2_ScopeCall122.fn (first s a counter).nextActivation []) r1.world
    let r3 := H (.child PV_THR2_ScopeCall123.fn (second (first s a counter) a thread).nextActivation [.boolean false]) r2.world
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H 29
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6ScopeData.pending s a parents counter thread panicked),
        r3.world,es ++ r1.events ++ r2.events ++ r3.events⟩,stack⟩ := by
  dsimp only
  rw [show 29 = 24 + 5 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ConstructorRun.from_entry base ctl P H s a parents b counter thread panicked w es stack leaf121 leaf122 leaf123,
    after_constructors base ctl (PV_FN_THREAD_f6Constructors.programs P) H s a parents b counter thread panicked _ _ stack live]

#print axioms issue
#print axioms after_constructors
#print axioms from_entry
end PV_FN_THREAD_f6ArcRequest
