# Stage 1: admitted observer

`ARX_AdmittedRuntime.runtime` records the original partial account computation
and retains its RunView exactly on cylinders containing their own `ARU_Support.At`.
That witness includes both runtime admissions, native successes, the approved
bank game and RuntimePersistence, plus issued-query agreement. `permitted_iff`
proves that cylinder membership is exactly own-world support; no all-world
support premise is introduced. `on_admitted` preserves the entire evaluation.
`excludes_poison` uses the retained no-admission result, not a new assumption.
This is a zero-extended, unnormalised admitted-world mean. Unsupported paths
still issue their original queries but return None, hence contribute no failure.

Attempts 001/002/004 passed; 003 was an excluded development error (missing
section-variable inclusion and wrong total/partial factory). Standard axioms
only in passing receipts. Each receipt includes command, revision, exact source
and dependency hashes, exit, wall, peak RSS, swap, cgroup and full axiom audit.
One capped scope at a time; no resource failures. No shipped source changed.
No numerical root bound or premise-removal claim is made at this stage.
