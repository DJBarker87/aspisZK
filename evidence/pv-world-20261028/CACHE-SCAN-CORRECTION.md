# Public-import scan correction

Attempt 36059 failed before declarations were checked: a cached transitive
import needed AspisV8R17.QM31WordResidues. The job's source scanner recognized
`import` but omitted Lean 4.32's `public import` (in QM31WordTower). This was
an error in this job's preflight inputs, not a host/launcher fault or a native
counterexample. It does not justify switching to another source cohort.

The corrected scanner recognizes public/private/meta modifiers and all modules
on an import line, after removing comments. The complete trust carrier source
closure increases from 827 to 830 project modules, with no unresolved source.
EJR/freeze/h5 precedence is unchanged. The OS cache selection is recomputed
with the full transitive closure before the failed consumer is retried.
Earlier dependency compiles are focused evidence; their former incomplete
cache-preflight claim is superseded. No privacy row or release credit rested
on them. The independently rebuilt FullFuns four-module extraction cone and
the reservation proofs do not use this omitted project import.

A retry of the unchanged consumer requires the newly selected missing import
artifact and records the new complete cache fingerprint. No shared source or
compiled object was edited. Private links rejected by the corrected closure
are unlinked before compilation to prevent writes through into any reused
cache. No key/account/wallet files are involved.
