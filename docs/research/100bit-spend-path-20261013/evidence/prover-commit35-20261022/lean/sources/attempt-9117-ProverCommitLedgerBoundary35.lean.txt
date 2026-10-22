import R1Z.ProverCommitEnvironment35
/-! Exact boundary of a status-only environment strategy. This is not an
obstruction to privacy: it is an obstruction to identifying a fixed native
create_new filesystem with a strategy that cannot inspect the request path.
The OS keeps contents private, but its duplicate result depends on that path.
No random or witness value is supplied to the strategy in D147's signature. -/
set_option autoImplicit false
namespace R1Z.ProverCommitLedgerBoundary35
open ProverCommitEnvironment35

/-- Honest create_new on an otherwise available filesystem. The keys here
are reservation paths, not wallet keys or file payloads. -/
def createStatus {Path : Type} [DecidableEq Path]
    (occupied : List Path) (path : Path) : Outcome :=
  if path ∈ occupied then .error .alreadyExists else .ok ()

/-- A fixed initial ledger containing one occupied and one fresh path forces
incompatible statuses after identical (index, kind, prior outcomes). This
holds for every prior history, including a single successful RNG call. -/
theorem no_status_only_create_law {Path : Type} [DecidableEq Path]
    (old fresh : Path) (distinct : fresh ≠ old) (history : History) :
    ¬ ∃ schedule : Schedule, ∀ path : Path,
      schedule history.length .create history = createStatus [old] path := by
  rintro ⟨schedule,law⟩
  have a := law old
  have b := law fresh
  have same := a.symm.trans b
  simp only [createStatus,List.mem_singleton,if_pos rfl,if_neg distinct] at same
  cases same

/-- Adaptive prior statuses do not repair the first-create obstruction: the
same successful RNG status history contains no returned bytes or path. -/
theorem rng_ok_does_not_determine_duplicate {Path : Type} [DecidableEq Path]
    (old fresh : Path) (distinct : fresh ≠ old) :
    ¬ ∃ schedule : Schedule, ∀ path : Path,
      schedule 1 .create [(.rng,.ok ())] = createStatus [old] path :=
  no_status_only_create_law old fresh distinct [(.rng,.ok ())]

#print axioms no_status_only_create_law
#print axioms rng_ok_does_not_determine_duplicate
end R1Z.ProverCommitLedgerBoundary35
