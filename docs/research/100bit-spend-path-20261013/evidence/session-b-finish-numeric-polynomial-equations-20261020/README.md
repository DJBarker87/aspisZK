# Both finish rounds retain their decoded polynomial equations

PROVED: each successful concrete polynomial candidate evaluation returns a canonical value and exposes the actual checked seven coefficient selections in descending Horner order, together with its decoded polynomial value. Successful S2 finish candidate execution derives these equations for both rounds and both numeric comparison guards, rather than retaining only polynomial-output canonicality. It also derives the successful newWeights/pair/dot calls, their comparison equalities and next=22. Canonical initial claim and alpha values remain hypotheses.

The source definitions and exact parsed-field/current-arithmetic owners are reused from the preceding packet. There is no abstract polynomial-operation semantics premise in this theorem. Original Rust Rev.fold equivalence, finish candidate equivalence/adoption, pairing/newWeights/dot semantics, caller reachability and deployed runtime are OPEN. This does not close R14 or the 100-bit soundness claim.

One focused NUC target, two standard-only axiom audits, -j1 -M4400/default proof options, High1GiB/Max2GiB/Swap0, no binaries or production edits.
