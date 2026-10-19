import R1VerifierCallBudget

/-! A conservative operational cost model, not an extraction of Rust.

Source labels: r1_semantic::verify_observed (1 + 27 triples),
verifier::Prepared::new (opening initialization, four scalar triples,
eight precomputed query pairs plus their absorb, and rho's triple),
query_with_geometry (three leaves and three six-parent paths),
checkpoint/resume (three hashes), and the post-G8 adapter's mutually
exclusive seven/five single-attempt PDA calls.

Each hash transition emits one arbitrary complete input/output pair, so
duplicates count. Silent transitions and terminal failures may occur at
every control point. Zero-length execution is allowed at every state:
theorems cover finite prefixes, not just completed or accepting runs.

The phase counters abstract internal control flow. Their Rust simulation,
all SHA-free callees, allocation/panic hooks and runtime behavior remain
OPEN; the interface at the end does not assert such a simulation. -/
set_option autoImplicit false
namespace AspisR1.VerifierPhaseCost

open VerifierCallBudget

abbrev Call := Bytes × Digest

inductive RegistryMode where
  | immutable | v1

inductive Route where
  | stage1Ten | stage1Eleven | stage2 (mode : RegistryMode)

inductive Failure where
  | rejected | panic | allocationFailure | computeExhausted | runtimeFailure

def Failure.stop : Failure → PrefixStop
  | .rejected => .rejected
  | .panic => .panic
  | .allocationFailure => .allocationFailure
  | .computeExhausted => .computeExhausted
  | .runtimeFailure => .runtimeFailure

inductive Tail where
  | checkpoint | finish

def Tail.cost : Tail → Nat
  | .checkpoint => 3
  | .finish => 0

inductive State where
  | semantic (k hashesLeft : Nat)
  | opening (k hashesLeft : Nat)
  | queries (next endIndex : Nat) (tail : Tail)
  | queryHashes (next endIndex : Nat) (tail : Tail) (hashesLeft : Nat)
  | checkpoint (hashesLeft : Nat)
  | pda (hashesLeft : Nat)
  | resume (hashesLeft : Nat)
  | accepted
  | failed (reason : Failure)

def State.stop : State → PrefixStop
  | .accepted => .accepted
  | .failed reason => reason.stop
  | _ => .running

/-- Potential depends on the control point and loop counter, not the trace. -/
def remaining : State → Nat
  | .semantic k n => n + openingBudget + queryBudget * k + 3
  | .opening k n => n + queryBudget * k + 3
  | .queries next endIndex tail => queryBudget * (endIndex - next) + tail.cost
  | .queryHashes next endIndex tail n =>
      n + queryBudget * (endIndex - (next + 1)) + tail.cost
  | .checkpoint n => n
  | .pda n => n + 3 + queryBudget * 22
  | .resume n => n + queryBudget * 22
  | .accepted | .failed _ => 0

def eventCost : Option Call → Nat
  | none => 0
  | some _ => 1

/-- Counters are local loop bounds. In particular, successful queries advance
`next` once; failure terminates instead of repeating the same query. -/
inductive Step : State → Option Call → State → Prop where
  | silent (s : State) : Step s none s
  | fail (s : State) (reason : Failure) : Step s none (.failed reason)
  | semanticHash (k n : Nat) (q : Call) :
      Step (.semantic k (n + 1)) (some q) (.semantic k n)
  | semanticDone (k : Nat) :
      Step (.semantic k 0) none (.opening k openingBudget)
  | openingHash (k n : Nat) (q : Call) :
      Step (.opening k (n + 1)) (some q) (.opening k n)
  | openingDone (k : Nat) :
      Step (.opening k 0) none (.queries 0 k .checkpoint)
  | beginQuery (next endIndex : Nat) (tail : Tail) (h : next < endIndex) :
      Step (.queries next endIndex tail) none
        (.queryHashes next endIndex tail queryBudget)
  | queryHash (next endIndex n : Nat) (tail : Tail) (q : Call) :
      Step (.queryHashes next endIndex tail (n + 1)) (some q)
        (.queryHashes next endIndex tail n)
  | queryDone (next endIndex : Nat) (tail : Tail) :
      Step (.queryHashes next endIndex tail 0) none
        (.queries (next + 1) endIndex tail)
  | queriesCheckpoint (next endIndex : Nat) (h : endIndex ≤ next) :
      Step (.queries next endIndex .checkpoint) none (.checkpoint 3)
  | queriesFinish (next endIndex : Nat) (h : endIndex ≤ next) :
      Step (.queries next endIndex .finish) none .accepted
  | checkpointHash (n : Nat) (q : Call) :
      Step (.checkpoint (n + 1)) (some q) (.checkpoint n)
  | checkpointDone : Step (.checkpoint 0) none .accepted
  | pdaHash (n : Nat) (q : Call) : Step (.pda (n + 1)) (some q) (.pda n)
  | pdaDone : Step (.pda 0) none (.resume 3)
  | resumeHash (n : Nat) (q : Call) :
      Step (.resume (n + 1)) (some q) (.resume n)
  /-- `resume` only checks `next ≤ 22`, not that stage1 produced the bytes.
  Values 0 and 22 are both included. All rejected checkpoints can stop earlier. -/
  | resumeDone (next : Nat) (h : next ≤ 22) :
      Step (.resume 0) none (.queries next 22 .finish)

theorem step_cost {s t : State} {q : Option Call} (h : Step s q t) :
    eventCost q + remaining t ≤ remaining s := by
  cases h <;>
    simp_all [eventCost, remaining, Tail.cost, openingBudget, queryBudget] <;>
    omega

/-- Every finite run segment, including prefixes ending within a hash phase. -/
inductive Exec : State → Trace → State → Prop where
  | nil (s : State) : Exec s [] s
  | silent {s u t : State} {tr : Trace} :
      Step s none u → Exec u tr t → Exec s tr t
  | hash {s u t : State} {q : Call} {tr : Trace} :
      Step s (some q) u → Exec u tr t → Exec s (q :: tr) t

theorem exec_cost {s t : State} {tr : Trace} (h : Exec s tr t) :
    tr.length + remaining t ≤ remaining s := by
  induction h with
  | nil => simp
  | silent hstep _ ih =>
      have hs := step_cost hstep
      simp only [eventCost] at hs
      omega
  | hash hstep _ ih =>
      have hs := step_cost hstep
      simp only [eventCost] at hs
      simp only [List.length_cons]
      omega

theorem exec_take {s t : State} {tr : Trace} (h : Exec s tr t) (n : Nat) :
    ∃ u, Exec s (tr.take n) u := by
  induction h generalizing n with
  | nil s => exact ⟨s, by simpa using (Exec.nil s)⟩
  | @silent s u t tr hstep _ ih =>
      obtain ⟨v, hv⟩ := ih n
      exact ⟨v, Exec.silent hstep hv⟩
  | @hash s u t q tr hstep _ ih =>
      cases n with
      | zero => exact ⟨s, by simpa using (Exec.nil s)⟩
      | succ n =>
          obtain ⟨v, hv⟩ := ih n
          exact ⟨v, by simpa using (Exec.hash hstep hv)⟩

def initial : Route → State
  | .stage1Ten => .semantic 10 semanticBudget
  | .stage1Eleven => .semantic 11 semanticBudget
  | .stage2 .immutable => .pda immutablePdaBudget
  | .stage2 .v1 => .pda v1PdaBudget

def routeBudget : Route → Nat
  | .stage1Ten => stage1Budget 10
  | .stage1Eleven => stage1Budget 11
  | .stage2 .immutable => stage2Budget
  | .stage2 .v1 => stage2V1Budget

theorem initial_cost (route : Route) : remaining (initial route) = routeBudget route := by
  cases route with
  | stage1Ten => rfl
  | stage1Eleven => rfl
  | stage2 mode => cases mode <;> rfl

theorem routeBudget_le (route : Route) : routeBudget route ≤ verifierBudget := by
  cases route with
  | stage1Ten => decide
  | stage1Eleven => decide
  | stage2 mode => cases mode <;> decide

theorem every_prefix_route_bound {route : Route} {tr : Trace} {t : State}
    (h : Exec (initial route) tr t) : tr.length ≤ routeBudget route := by
  have hc := exec_cost h
  rw [initial_cost] at hc
  omega

theorem every_prefix_le_472 {route : Route} {tr : Trace} {t : State}
    (h : Exec (initial route) tr t) : tr.length ≤ 472 := by
  have hr := every_prefix_route_bound h
  have hb := routeBudget_le route
  rw [verifierBudget_value] at hb
  omega

/-- A suffix bound for arbitrary checkpoint counters, with no provenance premise. -/
theorem arbitrary_checkpoint_query_prefix {next : Nat} {tr : Trace} {t : State}
    (_hnext : next ≤ 22) (h : Exec (.queries next 22 .finish) tr t) :
    tr.length ≤ 21 * (22 - next) := by
  have hc := exec_cost h
  simp only [remaining, Tail.cost, queryBudget, Nat.add_zero] at hc
  omega

/-- Covers explicit rejection, panic, allocation, compute and runtime failures. -/
theorem failed_prefix_le_472 {route : Route} {tr : Trace} {reason : Failure}
    (h : Exec (initial route) tr (.failed reason)) : tr.length ≤ 472 :=
  every_prefix_le_472 h

/-- Running prefixes may end at any state, including immediately before exit. -/
def ModelPrefix (route : Route) (stop : PrefixStop) (tr : Trace) : Prop :=
  ∃ t, Exec (initial route) tr t ∧ (stop = .running ∨ stop = t.stop)

theorem model_prefix_closed {route : Route} {stop : PrefixStop} {pre post : Trace}
    (h : ModelPrefix route stop (pre ++ post)) : ModelPrefix route .running pre := by
  obtain ⟨t, hexec, _⟩ := h
  obtain ⟨u, hu⟩ := exec_take hexec pre.length
  exact ⟨u, by simpa only [List.take_left] using hu, Or.inl rfl⟩

theorem model_prefix_bound {route : Route} {stop : PrefixStop} {tr : Trace}
    (h : ModelPrefix route stop tr) : tr.length ≤ verifierBudget := by
  obtain ⟨t, hexec, _⟩ := h
  rw [verifierBudget_value]
  exact every_prefix_le_472 hexec

/-- OPEN source interface. This must be derived from the actual source/runtime
semantics, including all hash callbacks, internal PDA digests, and abort paths.
It preserves the complete call trace, not merely its length. No instance,
axiom, or claim of extraction is supplied in this file. -/
structure SourceSimulation {Cfg Input : Type}
    (SourcePrefix : PrefixRelation Cfg Input) (Admitted : Cfg → Input → Prop)
    (routeOf : Cfg → Input → Route) : Prop where
  preservesPrefix : ∀ cfg input H stop tr,
    Admitted cfg input → SourcePrefix cfg input H stop tr →
      ModelPrefix (routeOf cfg input) stop tr

theorem source_count_of_simulation {Cfg Input : Type}
    {SourcePrefix : PrefixRelation Cfg Input} {Admitted : Cfg → Input → Prop}
    {routeOf : Cfg → Input → Route}
    (simulation : SourceSimulation SourcePrefix Admitted routeOf) :
    AllPrefixCount SourcePrefix Admitted verifierBudget := by
  intro cfg input H stop tr hadmitted hsource
  exact model_prefix_bound (simulation.preservesPrefix cfg input H stop tr hadmitted hsource)

theorem source_obligation_of_simulation {Cfg Input : Type}
    {SourcePrefix : PrefixRelation Cfg Input} {Admitted : Cfg → Input → Prop}
    {routeOf : Cfg → Input → Route}
    (hclosed : PrefixClosed SourcePrefix)
    (simulation : SourceSimulation SourcePrefix Admitted routeOf) :
    SourceCountObligation SourcePrefix Admitted :=
  ⟨hclosed, source_count_of_simulation simulation⟩

#print axioms step_cost
#print axioms exec_cost
#print axioms exec_take
#print axioms initial_cost
#print axioms routeBudget_le
#print axioms every_prefix_route_bound
#print axioms every_prefix_le_472
#print axioms arbitrary_checkpoint_query_prefix
#print axioms failed_prefix_le_472
#print axioms model_prefix_bound
#print axioms model_prefix_closed
#print axioms source_count_of_simulation
#print axioms source_obligation_of_simulation

end AspisR1.VerifierPhaseCost
