import PV_FN_THREAD_f6Reply121
import PV_THR2_ScopeCall122
import PV_THR2_ScopeCall123
import PV_THR2_ScopeStorage
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Constructors
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Only the three LEAF constructors are abstracted. In particular the actual
ScopeData Arc constructor at1916 remains structured in P. -/
def programs (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data) := by
  classical exact if fn = PV_THR2_ScopeCall121.fn ∨ fn = PV_THR2_ScopeCall122.fn ∨
    fn = PV_THR2_ScopeCall123.fn then none else P fn

theorem resolves (P : Data → Option PV_STX2_SliceSyntax.Program) :
    programs P PV_THR2_ScopeCall121.fn = none ∧
    programs P PV_THR2_ScopeCall122.fn = none ∧
    programs P PV_THR2_ScopeCall123.fn = none := by
  simp [programs]

/-- All three calls consume the full reply at the actual saved request. This
helper does not select a returned branch or assume a frame of the world. -/
theorem full_reply {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (rest : List PV_STX2_SliceSyntax.Node) (fn : Data) (vs : List Data) (dest : Nat)
    (w : W) (es : List E) (stack : List Config)
    (child : P fn = none) (ordinary : fn ≠ PV_THR2_Catch219Call318.fn) :
    let c := PV_THR2_StaticCall.pending s a parents rest fn vs dest
    let q := PV_THR2_ChildBoundary.delivered B c
      (PV_THR2_StaticReply.wait s fn vs dest) (H (.child fn s.nextActivation vs) w)
    PV_THR2_IntrinsicState.step B K P H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  dsimp only
  rw [PV_THR2_IntrinsicCompatible.step B K P H _ w es stack (by
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, tail⟩⟩⟩⟩ <;>
      simp [PV_THR2_Catch316Segment.select,PV_THR2_StaticCall.pending,ordinary]),
    PV_THR2_StaticReply.full_reply B K P H s a parents rest fn vs dest w child]

/-- Source ids, rather than erased-value selection, exclude intrinsic318. -/
theorem ordinary122 : PV_THR2_ScopeCall122.fn ≠ PV_THR2_Catch219Call318.fn := by
  intro eq
  have ids := congrArg PV_THR2_OffPath.functionId eq
  change (some 122 : Option Nat) = some 318 at ids
  cases ids

theorem ordinary123 : PV_THR2_ScopeCall123.fn ≠ PV_THR2_Catch219Call318.fn := by
  intro eq
  have ids := congrArg PV_THR2_OffPath.functionId eq
  change (some 123 : Option Nat) = some 318 at ids
  cases ids

/-- From the continuation after121, execute source1783 and issue1820. -/
theorem request122 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) P H 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 17},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_THR2_ScopeCall122.pending (write s ⟨a,6,[]⟩ none) a parents),w,es⟩,stack⟩ := by
  dsimp only
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step _ _ P H _ w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl),PV_THR2_ScopeStorage.thread_local]
  simp only [List.append_nil]
  rw [PV_THR2_IntrinsicCompatible.step _ _ P H _ w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl),PV_THR2_ScopeCall122.issue]
  simp only [List.append_nil]

/-- From the continuation after122, execute source1821 and issue1875. -/
theorem request123 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) P H 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 19},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_THR2_ScopeCall123.pending (write s ⟨a,7,[]⟩ none) a parents),w,es⟩,stack⟩ := by
  dsimp only
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step _ _ P H _ w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl),PV_THR2_ScopeStorage.panic_local]
  simp only [List.append_nil]
  rw [PV_THR2_IntrinsicCompatible.step _ _ P H _ w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl),PV_THR2_ScopeCall123.issue]
  simp only [List.append_nil]

/-- A source-storage/call pair followed by an arbitrary FULL reply of122. -/
theorem reply122 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    let t := write s ⟨a,6,[]⟩ none
    let q := PV_THR2_ChildBoundary.delivered B (PV_THR2_ScopeCall122.pending t a parents)
      (PV_THR2_StaticReply.wait t PV_THR2_ScopeCall122.fn [] 6)
      (H (.child PV_THR2_ScopeCall122.fn t.nextActivation []) w)
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 17},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  dsimp only
  rw [show 3 = 2 + 1 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    request122 base ctl (programs P) H s a parents b w es stack]
  simp only [PV_THR2_IntrinsicState.advance]
  exact full_reply _ _ _ H _ a parents _ _ [] 6 w es stack (resolves P).2.1 ordinary122

/-- The third constructor also retains all failure/divergence/pending answers. -/
theorem reply123 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    let t := write s ⟨a,7,[]⟩ none
    let q := PV_THR2_ChildBoundary.delivered B (PV_THR2_ScopeCall123.pending t a parents)
      (PV_THR2_StaticReply.wait t PV_THR2_ScopeCall123.fn [.boolean false] 7)
      (H (.child PV_THR2_ScopeCall123.fn t.nextActivation [.boolean false]) w)
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 19},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  dsimp only
  rw [show 3 = 2 + 1 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    request123 base ctl (programs P) H s a parents b w es stack]
  simp only [PV_THR2_IntrinsicState.advance]
  exact full_reply _ _ _ H _ a parents _ _ [.boolean false] 7 w es stack (resolves P).2.2 ordinary123

#print axioms resolves
#print axioms full_reply
#print axioms ordinary122
#print axioms ordinary123
#print axioms request122
#print axioms request123
#print axioms reply122
#print axioms reply123
end PV_FN_THREAD_f6Constructors
