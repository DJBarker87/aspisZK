# Stage A — unconditional marks audit

Status: source schedule and successful source fixture checked. S2 target not established.

## Before and after

Before (`S2W_TraceSplice.FirstMarks.source`):

```
∀ event, mark event = some false → ∃ fs,
  (events port event).map project = firstTrace fs
```

After (`Op5T_Marks.FirstMarks.source`):

```
∀ event, mark event = some false → accepted ops event → ∃ fs,
  (events port event).map project = firstTrace fs
```

`accepted` tests the ACTUAL invoked call's Rust Ok, including its actual
arguments; it does not trust an arbitrary typed event's claimed return.
SecondMarks is restated analogously. The old marks imply the new ones.
No theorem about the unchanged original accepted-pair interface has yet been
claimed under only the new marks.

The original premise is unconditional even though accepted_pair_claims,
Op3I and Tx2I subsequently use it on an accepted pair. Their outer acceptance
premises do not narrow the quantifier hidden in the marks record. The checked
Op5C wrong-split source branch has no batch/query/save suffix. Consequently
the old marks plus a GLOBAL source-site association are inconsistent for that
branch. This does NOT show that FirstMarks alone is inconsistent: an arbitrary
port can invent suffix marks. Claiming logical vacuity without the missing
source association would overstate the counterexample.

## Premise audit

The replacement adds an antecedent, strictly restricting the observations for
which layout is required; it does not add source success as a global premise.
No metric, security event, root-authentication criterion, input carrier or
native dictionary is changed. This is the lead-authorised interface correction,
not an established implementation of ChildConeJoin. Rejected oracle effects
remain security-experiment obligations; no permission to erase them follows.

The source marking theorem derives batch/query/save sites from an actual
successful typed execution of the literal extracted TX1. The consistency
fixture will preserve installed shape and finish, while explicitly selecting
remaining leaf operations. It is not a production multiproof fixture, an SDK
accepted spend, or joint inhabitation of all native/cryptographic hypotheses.

## Validation and scope

13/80 Lean attempts (five unchanged missing-dependency builds), 0/40 Kani.
The initial launcher preflight found missing VTop_Order and launched no Lean;
the missing unchanged dependency chain was built one module per capped scope.
Attempt001 hit a Lean heartbeat limit, not the external timeout: replacement007
changed the proof to a function projection, and passed. Failed008–012 are
retained and excluded; fixture013 passes. No unchanged timed-out retry, cap
increase or package replay. All final audits are standard axioms only.

Final Mark check007: exit0, wall1.941080135s, peak5168124KiB, swap0.
Final fixture013: exit0, wall1.928995977s, peak5168860KiB, swap0.
Full revision, source/dependency hashes, exact target/command, caps and axioms
are in each receipt. This is focused validation against the inherited coherent
SInt2 object selection, not a new frozen release replay.

No shipped file or cfg(kani) module changed; the ELF rebuild trigger did not
fire. The inherited default f8c0ec72…, devnet63ad3e9c…, Pool121f3e29… pins
were not reproduced. No key or sibling-prefix files changed.

Remaining: the source-derived site theorem is not yet an implementation of
the success-conditioned ChildConeJoin port for the top SDK dictionary. The
original accepted-pair theorem is unchanged and still requires its old marks.
Stage B must make that association concrete before claiming batch/Q1 closure.
