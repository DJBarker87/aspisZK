import PV_FN_THREAD_f6Constructors
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ConstructorRun
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6Constructors

def first (s : Store Data) (a : Nat) (v : Data) :=
  PV_THR2_StaticReply.returnedStore (PV_THR2_ScopePrologue.prepared s a) a [.number 0] 5 v

def second (s : Store Data) (a : Nat) (v : Data) :=
  PV_THR2_StaticReply.returnedStore (write s ⟨a,6,[]⟩ none) a [] 6 v

def third (s : Store Data) (a : Nat) (v : Data) :=
  PV_THR2_StaticReply.returnedStore (write s ⟨a,7,[]⟩ none) a [.boolean false] 7 v

/-- Returned branch of the already arbitrary FULL leaf121 reply. The payload,
post-world and event suffix remain arbitrary. No structured124 abstraction. -/
theorem returned121 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (v : Data)
    (w : W) (es : List E) (stack : List Config)
    (leaf121 : (H (.child PV_THR2_ScopeCall121.fn (PV_THR2_ScopePrologue.prepared s a).nextActivation [.number 0]) w).answer = .returned (.ok v)) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    let r := H (.child PV_THR2_ScopeCall121.fn (PV_THR2_ScopePrologue.prepared s a).nextActivation [.number 0]) w
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H 18
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 17},parents,
        first s a v⟩,r.world,es ++ r.events⟩,stack⟩ := by
  dsimp only
  rw [show 18 = 17 + 1 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6Entry.request base ctl (programs P) H s a parents b w es stack]
  simp only [PV_THR2_IntrinsicState.advance]
  simp only [PV_THR2_ScopeCall121.pending]
  rw [full_reply _ _ _ H (PV_THR2_ScopePrologue.prepared s a) a parents (PV_THR2_F6.live.body.drop 17) _ [.number 0] 5 w es stack
    (resolves P).1 PV_FN_THREAD_f6Reply121.not_intrinsic]
  rw [PV_THR2_RunEntryReturned.returned_eta _ v leaf121]
  rfl

/-- Returned branch of the already arbitrary FULL leaf122 reply. The payload,
post-world and event suffix remain arbitrary. No structured124 abstraction. -/
theorem returned122 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (v : Data)
    (w : W) (es : List E) (stack : List Config)
    (leaf122 : (H (.child PV_THR2_ScopeCall122.fn (write s ⟨a,6,[]⟩ none).nextActivation []) w).answer = .returned (.ok v)) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    let r := H (.child PV_THR2_ScopeCall122.fn (write s ⟨a,6,[]⟩ none).nextActivation []) w
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 17},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 19},parents,
        second s a v⟩,r.world,es ++ r.events⟩,stack⟩ := by
  dsimp only
  rw [reply122 base ctl P H s a parents b w es stack]
  rw [PV_THR2_RunEntryReturned.returned_eta _ v leaf122]
  rfl

/-- Returned branch of the already arbitrary FULL leaf123 reply. The payload,
post-world and event suffix remain arbitrary. No structured124 abstraction. -/
theorem returned123 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (v : Data)
    (w : W) (es : List E) (stack : List Config)
    (leaf123 : (H (.child PV_THR2_ScopeCall123.fn (write s ⟨a,7,[]⟩ none).nextActivation [.boolean false]) w).answer = .returned (.ok v)) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    let r := H (.child PV_THR2_ScopeCall123.fn (write s ⟨a,7,[]⟩ none).nextActivation [.boolean false]) w
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 19},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 21},parents,
        third s a v⟩,r.world,es ++ r.events⟩,stack⟩ := by
  dsimp only
  rw [reply123 base ctl P H s a parents b w es stack]
  rw [PV_THR2_RunEntryReturned.returned_eta _ v leaf123]
  rfl

/-- Actual own-entry stores/requests; no future read or representation premise.
This is the returned prefix through the three LEAF constructors, not f6 closure. -/
theorem from_entry {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (counter thread panicked : Data) (w : W) (es : List E) (stack : List Config)
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
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H 24
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 21},parents,
        third (second (first s a counter) a thread) a panicked⟩,
        r3.world,es ++ r1.events ++ r2.events ++ r3.events⟩,stack⟩ := by
  dsimp only
  rw [show 24 = 18 + (3 + 3) from rfl,PV_THR2_IntrinsicComposition.advance_add,
    returned121 base ctl P H s a parents b counter w es stack leaf121]
  simp only [show (PV_THR2_ScopePrologue.prepared s a).nextActivation = s.nextActivation from rfl]
  rw [PV_THR2_IntrinsicComposition.advance_add,
    returned122 base ctl P H (first s a counter) a parents b thread _ _ stack leaf122]
  have nextWrite (t : Store Data) (p : Address) (v : Option Data) :
      (write t p v).nextActivation = t.nextActivation := rfl
  simp only [nextWrite]
  rw [returned123 base ctl P H (second (first s a counter) a thread) a parents b panicked _ _ stack leaf123]
  simp only [nextWrite]

#print axioms returned121
#print axioms returned122
#print axioms returned123
#print axioms from_entry
end PV_FN_THREAD_f6ConstructorRun
