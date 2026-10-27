# Symbolic dictionary congruence method

`PV_RE_DictGenerator` constructs kernel-checked Eq proof terms by structural
congruence of each named definition's *symbolic function body*. Each immediate
callee is replaced using its separately named dictionary congruence theorem.
Lambdas use funext. `Lean.Order.fix` uses congruence of its functional and proof
irrelevance of the monotonicity certificate; no recursive equation is evaluated.
No concrete input, array, numeral, recurrence, or complete run is normalized.
Type erasure in the `Payload` alias is checked only at sort-valued expressions.

A suffix is copied with an unchanged body into `PV_RE_DictSuffixNNN.continueAfter`.
The generator checks its dependency support independently, and also checks the
corresponding original full source function. These are semantic support
supersets; minimality and actual invocation are not claimed.

The retained retry/control definitions are repackaged (only import lines removed)
into one private source module `PV_RE_RetryRestored`. Original declaration names,
statements and proof terms are preserved; source hashes are recorded. This avoids
rebuilding ten unchanged module headers after the previous cache cleanup. It is
not a clean release manifest replay and does not overwrite any shared object.
