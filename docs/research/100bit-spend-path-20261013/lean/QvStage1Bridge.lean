import QvStage1Count
import R1VerifierPhaseCost

/-! Cost embedding, not a current compact-Rust extraction. The existing
SourceSimulation cannot be specialized to the binary call trace: its Route
and initial state still encode the eight-way budget. -/
set_option autoImplicit false
namespace AspisR1.QvStage1
open VerifierCallBudget VerifierPhaseCost

theorem distinct_firstReads_bound {Pf : Type}
    (v : AspisV8R19.MemoizedProgramLaw.View Bytes Digest (Pf × Bool))
    (h : CountedTrace 10 v.1) : FS2.distinctFirstReads v ≤ 595 := by
  have hc := countedTrace_bound h
  rw [stage1Budget_ten] at hc
  exact distinctFirstReads_of_totalCalls v 595 hc

/-- Reuse the existing hash-step semantics with a binary initial potential.
This forgets termination labels; it is a count embedding only. -/
theorem embed_trace (tr : Trace) (n : Nat) (h : tr.length ≤ n) :
    Exec (.checkpoint n) tr (.checkpoint (n - tr.length)) := by
  induction tr generalizing n with
  | nil => simpa using Exec.nil (.checkpoint n)
  | cons q tr ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      have ht : tr.length ≤ n := by simpa using h
      have hs := Exec.hash (Step.checkpointHash n q) (ih n ht)
      simpa only [List.length_cons, Nat.add_sub_add_right] using hs

/-- Named obligation for the admitted current source, including failed and
suspended prefixes. It must be discharged by call-log extraction, not by
postulating the numerical bound itself. -/
def SourceCoverage {Cfg Input : Type}
    (SourcePrefix : PrefixRelation Cfg Input) (Admitted : Cfg → Input → Prop) : Prop :=
  ∀ cfg input H stop tr, Admitted cfg input → SourcePrefix cfg input H stop tr →
    CountedTrace 10 tr

/-- A partial binary replacement for SourceSimulation.preservesPrefix.
It preserves the complete trace in the old Step/Exec semantics, but uses
595 units of initial potential and does not assert stop-label refinement. -/
structure BinaryCountSimulation {Cfg Input : Type}
    (SourcePrefix : PrefixRelation Cfg Input) (Admitted : Cfg → Input → Prop) : Prop where
  preservesPrefix : ∀ cfg input H stop tr,
    Admitted cfg input → SourcePrefix cfg input H stop tr →
    ∃ t, Exec (.checkpoint (stage1Budget 10)) tr t

theorem simulation_of_coverage {Cfg Input : Type}
    {SourcePrefix : PrefixRelation Cfg Input} {Admitted : Cfg → Input → Prop}
    (coverage : SourceCoverage SourcePrefix Admitted) :
    BinaryCountSimulation SourcePrefix Admitted := by
  constructor
  intro cfg input H stop tr ha hs
  exact ⟨_, embed_trace tr _ (countedTrace_bound (coverage cfg input H stop tr ha hs))⟩

theorem source_count_of_binary_simulation {Cfg Input : Type}
    {SourcePrefix : PrefixRelation Cfg Input} {Admitted : Cfg → Input → Prop}
    (simulation : BinaryCountSimulation SourcePrefix Admitted) :
    AllPrefixCount SourcePrefix Admitted 595 := by
  intro cfg input H stop tr ha hs
  obtain ⟨t, ht⟩ := simulation.preservesPrefix cfg input H stop tr ha hs
  have h := exec_cost ht
  simp only [remaining, stage1Budget_ten] at h
  omega

/-- Concrete count counterexample to reusing the old stage-1 route.
The measured 595-call traces cannot have its ModelPrefix certificate. -/
theorem old_stage1_model_excludes_595 (tr : Trace) (stop : PrefixStop)
    (h : tr.length = 595) : ¬ ModelPrefix .stage1Ten stop tr := by
  intro hm
  obtain ⟨t, ht, _⟩ := hm
  have hc := every_prefix_route_bound ht
  change tr.length ≤ VerifierCallBudget.stage1Budget 10 at hc
  rw [VerifierCallBudget.stage1Budget_ten, h] at hc
  omega

#print axioms distinct_firstReads_bound
#print axioms embed_trace
#print axioms simulation_of_coverage
#print axioms source_count_of_binary_simulation
#print axioms old_stage1_model_excludes_595
end AspisR1.QvStage1
