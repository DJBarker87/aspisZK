import PV_LIB_A_C18_A_PureCalls
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Range165
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
/-- ONE named documented-semantics fact for exact opaque f165 at f15/3420.
core/iter/traits/collect.rs: IntoIterator for I: Iterator returns self.
Both pinned toolchains' bodies/hashes are in RANGE165_SEMANTICS.json.
This is a lower source-semantics obligation, never an endpoint premise or
claimed native correspondence. Other reply arms remain arbitrary. -/
def PV_THR2_LibrarySemantics_RangeIntoIter165 {E : Type}
    (C : Carrier OWNER Data) (D : Effects) (H : Backend E) : Prop :=
  ∀ e w original, e.arguments = [original] →
    let d := PV_W1_NativeLeaves.entry165 e e.arguments
    Confined C d w (D d w) (fun _ => False) ∧
    ∀ v,
      let r : Reply OWNER E Data := PV_THR2_OwnUniformResourceHandler.lift H
        (.child d.callee d.store.nextActivation d.arguments) w;
      r.answer = .returned (.ok v) → v = original ∧ r.world = w ∧ r.events = []

def replyModel {E : Type} (original : Data) (w : OWNER) (r : Reply OWNER E Data) :=
  match r.answer with
  | .returned (.ok _) => (⟨.returned (.ok original),w,[]⟩ : Reply OWNER E Data)
  | _ => r

def model {E : Type} (C : Carrier OWNER Data) (H : Backend E)
    (e : Entry) (w : OWNER) (es : List E) (original : Data) :=
  let d := PV_W1_NativeLeaves.entry165 e e.arguments
  PV_LIB.observe (deliver C d (replyModel original w
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w)) es)
def law {E : Type} (C : Carrier OWNER Data) (H : Backend E)
    (e : Entry) (w : OWNER) (es : List E) (original : Data)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model C H e w es original

theorem reply_exact {E : Type} (original : Data) (w : OWNER) (r : Reply OWNER E Data)
    (semantics : ∀ v, r.answer = .returned (.ok v) → v = original ∧ r.world = w ∧ r.events = []) :
    r = replyModel original w r := by
  cases ans : r.answer with
  | returned result =>
    cases result with
    | ok v =>
      obtain ⟨rfl,world,events⟩ := semantics v ans
      rcases r with ⟨answer,post,suffix⟩
      simp only at ans world events
      subst answer
      subst post
      subst suffix
      rfl
    | fail err => simp [replyModel,ans]
    | div => simp [replyModel,ans]
  | fault f => simp [replyModel,ans]
  | pending => simp [replyModel,ans]

/-- CLOSED165 is instantiated, then its exact source meaning binds the graph.
No identity delta or successful-child assumption is selected. -/
theorem certified {E : Type} (C : Carrier OWNER Data) (D : Effects) (H : Backend E)
    (semantics : PV_THR2_LibrarySemantics_RangeIntoIter165 C D H)
    (e : Entry) (w : OWNER) (es : List E) (original : Data)
    (args : e.arguments = [original]) (pre : PV_W1_NativeLeaves.Pre e w) :
    law C H e w es original
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry165 e e.arguments) H w es
        (D (PV_W1_NativeLeaves.entry165 e e.arguments) w))) ∧
    PV_W1_NativeLeaves.Post165 C e H w e.arguments es
      (D (PV_W1_NativeLeaves.entry165 e e.arguments) w) := by
  refine ⟨?_,PV_W1_NativeLeaves.f165 C e H w e.arguments es _ pre⟩
  have facts := semantics e w original args
  let d := PV_W1_NativeLeaves.entry165 e e.arguments
  have pure := PV_FN_THREAD_f170_ActualNativeFrames.pureStore C d w (D d w) facts.1
  have after : PV_W1_ArgumentEffects.afterEffects C d w (D d w) = d := by
    unfold PV_W1_ArgumentEffects.afterEffects
    rw [pure]
  unfold law model PV_LIB_NativeGraph.internalModel
  rw [after]
  exact congrArg (fun reply => PV_LIB.observe (deliver C d reply es))
    (reply_exact original w _ facts.2)

/-- The unchanged CLOSED contract alone admits a nonidentity returned value.
This is an interface diagnostic, not a claim about the Rust implementation. -/
def nullBackend {E : Type} : Backend E := fun _ w => ⟨.returned (.ok .null),w,[]⟩
theorem old_contract_allows_null {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (w : OWNER) (es : List E) (original : Data) (changes : Address → Option Data)
    (pre : PV_W1_NativeLeaves.Pre e w) :
    PV_W1_NativeLeaves.Post165 C e (nullBackend (E := E)) w [original] es changes ∧
    (PV_THR2_OwnUniformResourceHandler.lift (nullBackend (E := E))
      (.child (PV_W1_NativeLeaves.entry165 e [original]).callee
        e.store.nextActivation [original]) w).answer = .returned (.ok .null) :=
  ⟨PV_W1_NativeLeaves.f165 C e _ w [original] es changes pre,rfl⟩
/-- The counterexample can use the actual source Range aggregate, not an
ill-typed scalar input. Its descriptor comes from emitted f15/node7. -/
def sourceRange (start finish : Nat) : Data :=
  let kind := match PV_THR2_F15.node7 with
    | .leaf (.aggregateMove _ _ kind _) => kind
    | _ => .null
  PV_THR2_KeyValues.pack kind [.number start,.number finish]
theorem sourceRange_not_null (start finish : Nat) : sourceRange start finish ≠ .null := by
  intro equal
  cases equal
def rangeBackend {E : Type} : Backend E := fun _ w =>
  ⟨.returned (.ok (sourceRange 2 5)),w,[]⟩
/-- Even a source-shaped Range reply need not equal the source argument. -/
theorem old_contract_allows_range {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (w : OWNER) (es : List E) (changes : Address → Option Data)
    (pre : PV_W1_NativeLeaves.Pre e w) :
    PV_W1_NativeLeaves.Post165 C e (rangeBackend (E := E)) w [sourceRange 1 3] es changes ∧
    (PV_THR2_OwnUniformResourceHandler.lift (rangeBackend (E := E))
      (.child (PV_W1_NativeLeaves.entry165 e [sourceRange 1 3]).callee
        e.store.nextActivation [sourceRange 1 3]) w).answer =
      .returned (.ok (sourceRange 2 5)) :=
  ⟨PV_W1_NativeLeaves.f165 C e _ w [sourceRange 1 3] es changes pre,rfl⟩
theorem sourceRange_distinct : sourceRange 1 3 ≠ sourceRange 2 5 := by
  intro h
  have first := congrArg (fun d => match d with
    | Data.object [_,(_,Data.array [Data.array [Data.number n],_])] => some n
    | _ => none) h
  change some 1 = some 2 at first
  cases first
#print axioms old_contract_allows_range
#print axioms sourceRange_distinct
#print axioms sourceRange_not_null
#print axioms reply_exact
#print axioms certified
#print axioms old_contract_allows_null
end PV_LIB_A_Range165
