# What the no-catch certificates mean

`PV_RE_NoCatchCore.NoCatch k` is exactly
`(∀ e, k (.fail e) = .fail e) ∧ k .div = .div`.
The new generator reads an elaborated source body without unfolding callees or
recurrences. At each Result bind it proves this predicate for the exact symbolic
continuation `fun r => r >>= k`, universally quantifying its source locals.
It does not reduce a whole run. Named certificates retain actual continuation
terms, not just names or hashes. All printed axioms must be standard.

These are local absorption certificates. Their existence alone is not a
whole-source theorem connecting a syntactic callback occurrence, its executed
prefix and the final caller Result. The source-closure scan is a separate
metaprogram measurement, not a Lean invocation theorem. It finds only
`Aeneas.Std.Result.ok` among Result constructors/recursors in the 695 examined
project bodies: no direct Result error match. That syntactic fact still needs
composition across reached branches, recursive fixed points and opaque
higher-order callback/trait boundaries before it supplies the `noCatch` premise
of `exclusion_by_poisoning` on the extracted whole caller. Do not equate the
local certificates or scan with that premise's discharge.

No instrumented trace semantics was added. The generic poisoning theorem keeps
an arbitrary `invoked` predicate and its absorption witness explicit; this is a
logical implication, not a definition of invocation, and not an established
source/fixture instance. No native association or successful input is assumed
without being listed as an unproved obligation.

`PV_RE_ShapePoison.poisoned_entry` is stronger for one actual source field:
poisoning op233 forces outer failure for every caller input. The distinguishing
success theorem remains conditional on a successful input, whose actual native
fixture non-vacuity is not proved. This single entry does not identify S.
