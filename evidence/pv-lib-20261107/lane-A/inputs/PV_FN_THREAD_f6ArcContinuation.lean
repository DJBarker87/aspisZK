import PV_FN_THREAD_f6ArcEntry
import PV_THR2_InlineChildReturn
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ArcContinuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6ConstructorRun PV_FN_THREAD_f6Constructors

/-- Actual body entry installed at1916, preserving its full caller/store. -/
def child (s : Store Data) (a : Nat) (parents : List Frame) (x y z : Data)
    (body : PV_STX2_SliceSyntax.Program) : Config :=
  let c := PV_FN_THREAD_f6ScopeData.pending s a parents x y z
  ⟨{activation := s.nextActivation+3,remaining := body.body},c.frame :: parents,c.store⟩

/-- First assume-guarantee stage: arbitrary FULL124 reply at source1916. The
CHILD resolver premise is local to this abstract stage; it is not an endpoint
premise or a claim about inline124's final store. -/
theorem full_reply {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (x y z : Data)
    (w : W) (es : List E) (stack : List Config)
    (abstract124 : P PV_THR2_ScopeArcCall.fn = none) :
    let t := PV_THR2_ScopeArcCall.before
      (PV_THR2_ScopeData.prepared (third (second (first s a x) a y) a z) a x y z) a
    let c := PV_FN_THREAD_f6ScopeData.pending s a parents x y z
    let q := PV_THR2_ChildBoundary.delivered B c
      (PV_THR2_StaticReply.wait t PV_THR2_ScopeArcCall.fn [PV_THR2_ScopeData.value x y z] 3)
      (H (.child PV_THR2_ScopeArcCall.fn t.nextActivation [PV_THR2_ScopeData.value x y z]) w)
    PV_THR2_IntrinsicState.step B K P H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  dsimp only
  have ordinary : PV_THR2_ScopeArcCall.fn ≠ PV_THR2_Catch219Call318.fn := by
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    change (some 124 : Option Nat) = some 318 at ids
    cases ids
  exact PV_FN_THREAD_f6Constructors.full_reply B K P H
    (PV_THR2_ScopeArcCall.before
      (PV_THR2_ScopeData.prepared (third (second (first s a x) a y) a z) a x y z) a)
    a parents (PV_THR2_F6.live.body.drop 26) PV_THR2_ScopeArcCall.fn
    [PV_THR2_ScopeData.value x y z] 3 w es stack abstract124 ordinary

/-- All finite prefixes of the structured124 child are composed from f6's
OWN entry. No body termination, result or world is assumed; the child contract
still to be supplied is `thread:f124` at this ScopeData configuration. -/
theorem child_prefix {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (counter thread panicked : Data) (w : W) (es : List E) (stack : List Config)
    (live : a < s.nextActivation)
    (body : PV_STX2_SliceSyntax.Program) (fuel : Nat)
    (resolved : P PV_THR2_ScopeArcCall.fn = some body)
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
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H (30 + fuel)
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩ =
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H fuel
      ⟨⟨.running (child s a parents counter thread panicked body),
        r3.world,es ++ r1.events ++ r2.events ++ r3.events⟩,stack⟩ := by
  dsimp only
  rw [show 30 + fuel = 29 + (1 + fuel) by omega,
    PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ArcRequest.from_entry base ctl P H s a parents b counter thread panicked w es stack live leaf121 leaf122 leaf123,
    PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6ArcEntry.enter _ _ P H s a parents counter thread panicked body _ _ stack resolved]
  rfl

/-- At a returned124 branch, consume the body's EXPLICIT final store. No old
call-store substitution erases its allocations, local writes or caller deltas.
The exact saved f6 destination3/continuation26 are derived from request1916. -/
theorem resume {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s t : Store Data) (a : Nat) (parents : List Frame) (x y z v : Data)
    (rest : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E) (stack : List Config) :
    let c := PV_FN_THREAD_f6ScopeData.pending s a parents x y z
    let pre := PV_THR2_ScopeArcCall.before
      (PV_THR2_ScopeData.prepared (third (second (first s a x) a y) a z) a x y z) a
    let q := PV_THR2_ChildBoundary.delivered B ⟨c.frame,parents,t⟩
      (PV_THR2_StaticReply.wait pre PV_THR2_ScopeArcCall.fn [PV_THR2_ScopeData.value x y z] 3)
      ⟨.returned (.ok v),w,es⟩
    PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running ⟨{activation := s.nextActivation+3,remaining := rest,completed := some (.ok v)},
        c.frame :: parents,t⟩,w,es⟩,stack⟩ = ⟨q,stack⟩ := by
  dsimp only
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step B K P H _ w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting _ rfl)]
  have eq := PV_THR2_InlineChildReturn.on_final_store B K P H t (s.nextActivation+3) 3 rest
    (PV_FN_THREAD_f6ScopeData.pending s a parents x y z).frame parents
    (PV_THR2_StaticReply.wait
      (PV_THR2_ScopeArcCall.before
        (PV_THR2_ScopeData.prepared (third (second (first s a x) a y) a z) a x y z) a)
      PV_THR2_ScopeArcCall.fn [PV_THR2_ScopeData.value x y z] 3) v w es rfl rfl
  exact congrArg (fun q : Prefix W E => (⟨q,stack⟩ : PV_THR2_IntrinsicState.State W E)) eq

#print axioms full_reply
#print axioms child_prefix
#print axioms resume
end PV_FN_THREAD_f6ArcContinuation
