# Session14 local binding correction — SPEC-C12
CHECKED55421, RawVec14.dispatch: the frozen FULL resolver expands the exact
f15/3398 token as F164.live; the exact f164/7894 token268 has no BODY.
A local native164 adapter therefore does not bind the constructor reached
inside that expansion. This was a session14 intermediate binding-dispatch
error, not a demonstrated error in the frozen contract statements. In
particular, no claim that164 was reached natively earns credit.

Before: PreludeValues14 binds164's empty Vec value, and Assembly14 selects
it, but Full.programs fn164 is Some F164.live. That adapter is dormant.
After: RawVec14 supplies268's empty RawVec graph with source359 raw/marker
tags, numeric pointer8/cap0 and no allocation; ReachedNative14 selects the
actual268 token before the old assembly, with the successful native trigger
in ReachedEnvironment14. The resolver, v2 table and every frozen statement
remain unchanged. RawBinding14 checks BODY priority and the final268 reply.

This is LOCAL source/native dispatch, not original reachability of7894,
physical-stack construction, a complete source-adequacy proof, or a negation
of the complete OwnInit existential. Work continued on the original prefix.
