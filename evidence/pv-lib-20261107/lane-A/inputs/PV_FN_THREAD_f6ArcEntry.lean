import PV_FN_THREAD_f6ArcRequest
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ArcEntry
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6ConstructorRun

/-- The request prefix preserves each pre-existing caller cell outside f6's
own activation. Fresh constructor/Arc argument activations are tracked rather
than erased from the explicit final store. -/
theorem frame (s : Store Data) (a : Nat) (parents : List Frame) (x y z : Data)
    (p : Address) (old : p.activation < s.nextActivation) (outside : p.activation ≠ a) :
    (PV_FN_THREAD_f6ScopeData.pending s a parents x y z).store.cells p = s.cells p := by
  have own (i : Nat) : p ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  have fresh (k j : Nat) : p ≠ (⟨s.nextActivation+k,j,[]⟩ : Address) := by
    intro eq
    exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le old (Nat.le_add_right _ _)))
      (congrArg Address.activation eq)
  have fresh0 (j : Nat) : p ≠ (⟨s.nextActivation,j,[]⟩ : Address) := fresh 0 j
  simp [PV_FN_THREAD_f6ScopeData.pending,PV_THR2_ScopeArcCall.pending,
    PV_THR2_ScopeArcCall.before,PV_THR2_ScopeData.prepared,
    first,second,third,PV_THR2_ScopePrologue.prepared,
    PV_THR2_StaticCall.pending,PV_THR2_StaticReply.returnedStore,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,own,fresh,fresh0,Nat.add_assoc]

/-- The move into124 leaves its source temporary absent, derived from entry
activation validity and freshness of the actual issued argument activation. -/
theorem moved (s : Store Data) (a : Nat) (parents : List Frame) (x y z : Data)
    (live : a < s.nextActivation) :
    (PV_FN_THREAD_f6ScopeData.pending s a parents x y z).store.cells ⟨a,4,[]⟩ = none := by
  have neq (j : Nat) : (⟨a,4,[]⟩ : Address) ≠ ⟨s.nextActivation+3,j,[]⟩ := by
    intro eq
    exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le live (Nat.le_add_right _ _)))
      (congrArg Address.activation eq)
  simp [PV_FN_THREAD_f6ScopeData.pending,PV_THR2_ScopeArcCall.pending,
    PV_THR2_ScopeArcCall.before,PV_THR2_ScopeData.prepared,
    first,second,third,PV_THR2_ScopePrologue.prepared,
    PV_THR2_StaticCall.pending,PV_THR2_StaticReply.returnedStore,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,neq,Nat.add_assoc]

/-- The B-y first-stage resolver does not mask structured124 at1916. -/
theorem resolves124 (P : Data → Option PV_STX2_SliceSyntax.Program) :
    PV_FN_THREAD_f6Constructors.programs P PV_THR2_ScopeArcCall.fn = P PV_THR2_ScopeArcCall.fn := by
  have n121 : PV_THR2_ScopeArcCall.fn ≠ PV_THR2_ScopeCall121.fn := by
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    change (some 124 : Option Nat) = some 121 at ids
    cases ids
  have n122 : PV_THR2_ScopeArcCall.fn ≠ PV_THR2_ScopeCall122.fn := by
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    change (some 124 : Option Nat) = some 122 at ids
    cases ids
  have n123 : PV_THR2_ScopeArcCall.fn ≠ PV_THR2_ScopeCall123.fn := by
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    change (some 124 : Option Nat) = some 123 at ids
    cases ids
  simp [PV_FN_THREAD_f6Constructors.programs,n121,n122,n123]

/-- Enter the actual saved124 request with its already installed ScopeData
argument and original saved caller. The dependency `thread:f124` must consume
THIS configuration and its explicit store, never a Packet-only surrogate. -/
theorem enter {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (x y z : Data)
    (body : PV_STX2_SliceSyntax.Program) (w : W) (es : List E) (stack : List Config)
    (resolved : P PV_THR2_ScopeArcCall.fn = some body) :
    let c := PV_FN_THREAD_f6ScopeData.pending s a parents x y z
    PV_THR2_IntrinsicState.advance B K (PV_FN_THREAD_f6Constructors.programs P) H 1
      ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := s.nextActivation+3,remaining := body.body},c.frame :: parents,c.store⟩,w,es⟩,stack⟩ := by
  dsimp only
  have r := PV_THR2_IntrinsicFrameEnter.run B K (PV_FN_THREAD_f6Constructors.programs P) H
    (PV_THR2_ScopeArcCall.before
      (PV_THR2_ScopeData.prepared (third (second (first s a x) a y) a z) a x y z) a)
    a parents [] (PV_THR2_F6.live.body.drop 26) PV_THR2_ScopeArcCall.fn
    [PV_THR2_ScopeData.value x y z] 3 body w es stack
    (by simp [PV_THR2_Catch316Segment.select,PV_THR2_IntrinsicFrameEnter.pending,
      PV_THR2_StaticReply.wait]) (by rw [resolves124]; exact resolved)
  exact r

#print axioms frame
#print axioms moved
#print axioms resolves124
#print axioms enter
end PV_FN_THREAD_f6ArcEntry
