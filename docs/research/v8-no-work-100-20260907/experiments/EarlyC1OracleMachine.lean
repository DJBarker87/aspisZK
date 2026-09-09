import AspisFormal.K1.V7BudgetedAdaptiveTargets

/-! A bounded sequential lazy oracle. Query choices depend on complete prior
answers. Cache hits are free; fresh budget exhaustion aborts. Its target tree
is constructed from the machine, rather than supplied as an event premise. -/
set_option autoImplicit false
set_option maxRecDepth 150
set_option maxHeartbeats 500000
namespace AspisV8.EarlyC1OracleMachine
open AspisK1.V7Tag73AdaptiveLazyOracle AspisK1.V7BudgetedAdaptiveTargets

variable {Key Output : Type} [DecidableEq Key] [DecidableEq Output]

abbrev Cache (Key Output : Type) := Key → Option Output

def insert (cache : Cache Key Output) (key : Key) (answer : Output) : Cache Key Output :=
  fun other => if other = key then some answer else cache other

inductive Strategy (Key Output : Type) : Nat → Type
  | halt {steps : Nat} : Strategy Key Output steps
  | query {steps : Nat} (key : Key) (next : Output → Strategy Key Output steps) :
      Strategy Key Output (steps + 1)

structure Result (Key Output : Type) where
  cache : Cache Key Output
  calls : List (Key × Output)
  aborted : Bool

def record (key : Key) (answer : Output) (result : Result Key Output) : Result Key Output :=
  { result with calls := (key, answer) :: result.calls }

def caps (targetCap : Nat) : Nat → List Nat
  | 0 => []
  | steps + 1 => targetCap :: caps targetCap steps

theorem caps_length (targetCap steps : Nat) : (caps targetCap steps).length = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [caps, List.length_cons, ih]

def run (targetCap : Nat) : {steps : Nat} → Strategy Key Output steps →
    Nat → Cache Key Output → FreshAnswerTape Output (caps targetCap steps).length → Result Key Output
  | _, .halt, _, cache, _ => ⟨cache, [], false⟩
  | _ + 1, .query key next, budget, cache, tape =>
      match cache key with
      | some answer => record key answer (run targetCap (next answer) budget cache tape.2)
      | none => match budget with
        | 0 => ⟨cache, [], true⟩
        | left + 1 => record key tape.1
            (run targetCap (next tape.1) left (insert cache key tape.1) tape.2)

def idle (targetCap : Nat) : (steps budget : Nat) →
    BudgetedCausalTargetTree Output targetCap (caps targetCap steps) budget
  | 0, budget => .done budget
  | steps + 1, budget => .free (fun _ => idle targetCap steps budget)

def targetTree (targets : Finset Output) (targetCap : Nat) (bound : targets.card ≤ targetCap) :
    {steps : Nat} → Strategy Key Output steps → (budget : Nat) → Cache Key Output →
      BudgetedCausalTargetTree Output targetCap (caps targetCap steps) budget
  | steps, .halt, budget, _ => idle targetCap steps budget
  | _ + 1, .query key next, budget, cache =>
      match cache key with
      | some answer => .free (fun _ => targetTree targets targetCap bound (next answer) budget cache)
      | none => match budget with
        | 0 => idle targetCap _ 0
        | left + 1 => .charged targets bound (fun answer =>
            targetTree targets targetCap bound (next answer) left (insert cache key answer))

theorem run_query_eq (targetCap : Nat) {steps : Nat} (key : Key)
    (next : Output → Strategy Key Output steps) (budget : Nat) (cache : Cache Key Output)
    (tape : FreshAnswerTape Output (caps targetCap (steps + 1)).length) :
    run targetCap (.query key next) budget cache tape =
      match cache key with
      | some answer => record key answer (run targetCap (next answer) budget cache tape.2)
      | none => match budget with
        | 0 => ⟨cache, [], true⟩
        | left + 1 => record key tape.1
            (run targetCap (next tape.1) left (insert cache key tape.1) tape.2) := by
  cases found : cache key <;> cases budget <;> simp only [run, found]

theorem targetTree_query_eq
    (targets : Finset Output) (targetCap : Nat) (bound : targets.card ≤ targetCap)
    {steps : Nat} (key : Key) (next : Output → Strategy Key Output steps)
    (budget : Nat) (cache : Cache Key Output) :
    targetTree targets targetCap bound (.query key next) budget cache =
      match cache key with
      | some answer => .free (fun _ => targetTree targets targetCap bound (next answer) budget cache)
      | none => match budget with
        | 0 => idle targetCap (steps + 1) 0
        | left + 1 => .charged targets bound (fun answer =>
            targetTree targets targetCap bound (next answer) left (insert cache key answer)) := by
  cases found : cache key <;> cases budget <;> simp only [targetTree, found]

theorem free_everHits {targetCap budget : Nat} {rest : List Nat}
    (next : Output → BudgetedCausalTargetTree Output targetCap rest budget)
    (tape : FreshAnswerTape Output (targetCap :: rest).length) :
    (BudgetedCausalTargetTree.free next).toCausal.everHits tape ↔
      (next tape.1).toCausal.everHits tape.2 := by
  cases budget <;> simp only [BudgetedCausalTargetTree.toCausal,
    CausalTargetTree.everHits, Finset.notMem_empty, false_or]

theorem run_preserves_cache (targetCap : Nat) {steps : Nat}
    (strategy : Strategy Key Output steps) (budget : Nat) (cache : Cache Key Output)
    (tape : FreshAnswerTape Output (caps targetCap steps).length)
    (key : Key) (answer : Output) (old : cache key = some answer) :
    (run targetCap strategy budget cache tape).cache key = some answer := by
  induction strategy generalizing budget cache key answer with
  | halt => exact old
  | @query steps queried next ih =>
      cases found : cache queried with
      | some cached =>
          simpa only [run_query_eq, found, record] using ih cached budget cache tape.2 key answer old
      | none =>
          cases budget with
          | zero => simpa only [run_query_eq, found] using old
          | succ budget =>
              have different : key ≠ queried := by
                intro same
                subst key
                rw [found] at old
                contradiction
              have preserved : insert cache queried tape.1 key = some answer := by
                simpa only [insert, if_neg different] using old
              simpa only [run_query_eq, found, record] using
                ih tape.1 budget (insert cache queried tape.1) tape.2 key answer preserved

theorem run_calls_cached (targetCap : Nat) {steps : Nat}
    (strategy : Strategy Key Output steps) (budget : Nat) (cache : Cache Key Output)
    (tape : FreshAnswerTape Output (caps targetCap steps).length)
    (key : Key) (answer : Output)
    (called : (key, answer) ∈ (run targetCap strategy budget cache tape).calls) :
    (run targetCap strategy budget cache tape).cache key = some answer := by
  induction strategy generalizing budget cache key answer with
  | halt => simp [run] at called
  | @query steps queried next ih =>
      cases found : cache queried with
      | some cached =>
          simp only [run_query_eq, found, record, List.mem_cons] at called ⊢
          rcases called with same | later
          · cases same
            apply run_preserves_cache
            exact found
          · exact ih cached budget cache tape.2 key answer later
      | none =>
          cases budget with
          | zero => simp only [run_query_eq, found, List.not_mem_nil] at called
          | succ budget =>
              simp only [run_query_eq, found, record, List.mem_cons] at called ⊢
              rcases called with same | later
              · cases same
                apply run_preserves_cache
                simp [insert]
              · exact ih tape.1 budget (insert cache queried tape.1) tape.2 key answer later

/-- The invariant is about a fixed ORIGINAL cache. A target-valued entry
not already in that cache cannot appear without a fresh charged hit. -/
theorem run_target_entry_from_old_or_hit
    (targets : Finset Output) (targetCap : Nat) (bound : targets.card ≤ targetCap)
    {steps : Nat} (strategy : Strategy Key Output steps) (budget : Nat)
    (cache original : Cache Key Output)
    (safe : ∀ key answer, cache key = some answer → answer ∈ targets →
      original key ≠ none)
    (tape : FreshAnswerTape Output (caps targetCap steps).length)
    (key : Key) (answer : Output)
    (final : (run targetCap strategy budget cache tape).cache key = some answer)
    (target : answer ∈ targets) :
    original key ≠ none ∨
      (targetTree targets targetCap bound strategy budget cache).toCausal.everHits tape := by
  induction strategy generalizing budget cache key answer with
  | halt => exact Or.inl (safe key answer final target)
  | @query steps queried next ih =>
      cases found : cache queried with
      | some cached =>
          have childFinal : (run targetCap (next cached) budget cache tape.2).cache key =
              some answer := by simpa only [run_query_eq, found, record] using final
          have child := ih cached budget cache safe tape.2 key answer childFinal target
          rcases child with old | hit
          · exact Or.inl old
          · apply Or.inr
            rw [targetTree_query_eq, found]
            exact (free_everHits _ tape).mpr hit
      | none =>
          cases budget with
          | zero =>
              have old : cache key = some answer := by simpa only [run_query_eq, found] using final
              exact Or.inl (safe key answer old target)
          | succ budget =>
              by_cases hit : tape.1 ∈ targets
              · apply Or.inr
                simp only [targetTree_query_eq, found, BudgetedCausalTargetTree.toCausal,
                  CausalTargetTree.everHits]
                exact Or.inl hit
              · have nextSafe : ∀ key answer, insert cache queried tape.1 key = some answer →
                    answer ∈ targets → original key ≠ none := by
                  intro other value entry isTarget
                  by_cases same : other = queried
                  · simp only [insert, if_pos same, Option.some.injEq] at entry
                    subst value
                    exact False.elim (hit isTarget)
                  · exact safe other value (by simpa only [insert, if_neg same] using entry) isTarget
                have childFinal : (run targetCap (next tape.1) budget
                    (insert cache queried tape.1) tape.2).cache key = some answer := by
                  simpa only [run_query_eq, found, record] using final
                have child := ih tape.1 budget (insert cache queried tape.1) nextSafe
                  tape.2 key answer childFinal target
                rcases child with old | later
                · exact Or.inl old
                · apply Or.inr
                  simp only [targetTree_query_eq, found, BudgetedCausalTargetTree.toCausal,
                    CausalTargetTree.everHits]
                  exact Or.inr later

def NewTargetEvent (targets : Finset Output) (targetCap : Nat)
    {steps : Nat} (strategy : Strategy Key Output steps) (budget : Nat)
    (cache : Cache Key Output)
    (tape : FreshAnswerTape Output (caps targetCap steps).length) : Prop :=
  ∃ key answer, cache key = none ∧
    (run targetCap strategy budget cache tape).cache key = some answer ∧ answer ∈ targets

theorem new_target_event_implies_constructed_tree_hit
    (targets : Finset Output) (targetCap : Nat) (bound : targets.card ≤ targetCap)
    {steps : Nat} (strategy : Strategy Key Output steps) (budget : Nat)
    (cache : Cache Key Output)
    (tape : FreshAnswerTape Output (caps targetCap steps).length)
    (bad : NewTargetEvent targets targetCap strategy budget cache tape) :
    (targetTree targets targetCap bound strategy budget cache).toCausal.everHits tape := by
  obtain ⟨key, answer, absent, final, target⟩ := bad
  have safe : ∀ key answer, cache key = some answer → answer ∈ targets → cache key ≠ none := by
    intro key answer entry _
    rw [entry]
    exact Option.some_ne_none _
  exact (run_target_entry_from_old_or_hit targets targetCap bound strategy budget cache cache
    safe tape key answer final target).resolve_left (by simpa [absent])

noncomputable def eventCount [Fintype Output]
    (targets : Finset Output) (targetCap : Nat)
    {steps : Nat} (strategy : Strategy Key Output steps) (budget : Nat)
    (cache : Cache Key Output) : Nat := by
  classical
  exact Fintype.card {tape : FreshAnswerTape Output (caps targetCap steps).length //
    NewTargetEvent targets targetCap strategy budget cache tape}

theorem new_target_event_count_le [Fintype Output]
    (targets : Finset Output) (targetCap : Nat) (bound : targets.card ≤ targetCap)
    {steps : Nat} (strategy : Strategy Key Output steps) (budget : Nat)
    (cache : Cache Key Output) :
    eventCount targets targetCap strategy budget cache ≤
      budget * targetCap * Fintype.card Output ^ (steps - 1) := by
  classical
  unfold eventCount
  let tree := targetTree targets targetCap bound strategy budget cache
  let injection :
      {tape : FreshAnswerTape Output (caps targetCap steps).length //
        NewTargetEvent targets targetCap strategy budget cache tape} →
      {tape : FreshAnswerTape Output (caps targetCap steps).length //
        tree.toCausal.everHits tape} := fun tape =>
    ⟨tape.1, new_target_event_implies_constructed_tree_hit
      targets targetCap bound strategy budget cache tape.1 tape.2⟩
  have injective : Function.Injective injection := by
    intro left right equal
    apply Subtype.ext
    exact congrArg
      (fun tape : {tape : FreshAnswerTape Output (caps targetCap steps).length //
          tree.toCausal.everHits tape} => tape.1) equal
  calc
    _ ≤ causalHitCount tree.toCausal :=
      Fintype.card_le_of_injective injection injective
    _ ≤ budget * targetCap * Fintype.card Output ^ ((caps targetCap steps).length - 1) :=
      budgeted_causal_hit_count_le tree
    _ = _ := by rw [caps_length]

#print axioms run_preserves_cache
#print axioms run_calls_cached
#print axioms run_target_entry_from_old_or_hit
#print axioms new_target_event_implies_constructed_tree_hit
#print axioms new_target_event_count_le
end AspisV8.EarlyC1OracleMachine
