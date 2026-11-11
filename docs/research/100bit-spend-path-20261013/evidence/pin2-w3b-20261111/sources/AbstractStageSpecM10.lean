import OptionWorkBoundM10

/-! Abstract, invariant-carrying stages. Composition checks no implementation
body. The eager stage and budget are indices, so clients can use projection
lemmas without reducing a concrete structure constructor. -/
set_option autoImplicit false
namespace AspisR1.AbstractStageSpecM10

structure StageSpec {A B : Type} (eager : A → Option B)
    (pre : A → Prop) (post : B → Prop) (budget : Nat → Nat) where
  run : A → Option B × Nat
  value : ∀ a, (run a).1 = eager a
  work : ∀ L a, pre a → (run a).2 ≤ budget L
  invariant : ∀ a b, pre a → (run a).1 = some b → post b

def seq {A B C : Type} {f : A → Option B} {g : B → Option C}
    {I : A → Prop} {J : B → Prop} {K : C → Prop} {F G : Nat → Nat}
    (s : StageSpec f I J F) (t : StageSpec g J K G) :
    StageSpec (fun a => (f a).bind g) I K (fun L => F L+G L+1) where
  run a := PublicParserWork.bind (s.run a) t.run
  value a := by
    rw [PublicParserWork.bind_value, s.value]
    exact congrArg (fun k => (f a).bind k) (funext t.value)
  work L a ha := OptionWorkBoundM10.bind_bound _ _ _ _ (s.work L a ha)
    (fun b hb => t.work L b (s.invariant a b ha hb))
  invariant a c ha hc := by
    rw [PublicParserWork.bind_value] at hc
    cases hb : (s.run a).1 with
    | none => simp only [hb,Option.bind_none] at hc; cases hc
    | some b =>
      rw [hb,Option.bind_some] at hc
      exact t.invariant b c (s.invariant a b ha hb) hc

/-- A pure writer stage promoted to an option stage without extra work. -/
def pureStage {A B : Type} (f : A → B) (run : A → B × Nat)
    (budget : Nat → Nat) (hv : ∀ a, (run a).1 = f a)
    (hw : ∀ L a, (run a).2 ≤ budget L) :
    StageSpec (fun a => some (f a)) (fun _ => True) (fun _ => True) budget where
  run a := (some (run a).1,(run a).2)
  value a := congrArg some (hv a)
  work L a _ := hw L a
  invariant _ _ _ _ := True.intro

/-- Generic sequence of any number of stages on one state type. Heterogeneous
pipelines use `seq`; this fold is its homogeneous sequence specialization. -/
def chain {A : Type} {I : A → Prop} :
    (fs : List (A → Option A)) →
    (bs : List (Nat → Nat)) →
    (ss : List ((f : A → Option A) × (b : Nat → Nat) × StageSpec f I I b)) →
    A → Option A × Nat
  | _, _, [], a => (some a,0)
  | fs, bs, s::ss, a => PublicParserWork.bind (s.2.2.run a) (chain fs bs ss)

theorem seq_value {A B C : Type} {f : A → Option B} {g : B → Option C}
    {I : A → Prop} {J : B → Prop} {K : C → Prop} {F G : Nat → Nat}
    (s : StageSpec f I J F) (t : StageSpec g J K G) (a : A) :
    ((seq s t).run a).1 = (f a).bind g := (seq s t).value a

theorem seq_work {A B C : Type} {f : A → Option B} {g : B → Option C}
    {I : A → Prop} {J : B → Prop} {K : C → Prop} {F G : Nat → Nat}
    (s : StageSpec f I J F) (t : StageSpec g J K G) (L : Nat) (a : A) (ha : I a) :
    ((seq s t).run a).2 ≤ F L+G L+1 := (seq s t).work L a ha

#print axioms seq_value
#print axioms seq_work
end AspisR1.AbstractStageSpecM10
