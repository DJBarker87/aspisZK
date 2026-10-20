# All cached-claim points: actual scalar reads and ordered source-loop trace

PROVED for the isolated cached-claim fission candidate; NOT ADOPTED. No production source or runtime changes.

CurrentClaimScalarNormalForm defines a scalar reader selecting sem.claims[point][l] for point0–2, sem.extra[l] for3, sem.before_z1[l] for4, and field(y1,l).c0 otherwise. Its body_eq_source theorem proves this normal form is equal, as a Result including failure/divergence and source error handling, to the unchanged extracted candidate loop body. The reader is a proof decomposition, not a further Rust rewrite. It uses nonnegativity of the actual unsigned point, and preserves semantic state, point and iterator.

CurrentClaimScalarBody derives the actual scalar read, g-array read and successful push from every successful continuation; a successful accepted terminal branch supplies the actual finishDot result. Push failure cannot become a successful continuation/accepted finish.

CurrentClaimScalarChain proves any successful whole29-iteration loop supplies an ordered chain of those exact reads and pushes and its actual final finishDot call. No independent child-success witnesses are assumptions. CurrentClaimScalarReads derives exactly29 ordered reads from successful helper execution at any point, with the actual initial newDot result, and separately pins successful semantic reads to the actual claims row/extra/before_z1 entries. This generalizes the earlier parser-backed point5 trace without dropping the source selection behavior.

Four focused NUC Lean4.32 -j1 -M4400 targets passed in2.307–2.408s at1GiB/2GiB/Swap0, with standard axioms only; exact source/object/owner/command/time/memory evidence retained. No whole-manifest replay or unchanged runtime replay.

OPEN: instantiating Dot callbacks with the concrete private accumulator and composing its returned field product equation over this same chain; canonical g from the actual gamma powers caller; semantic Verified source/payload correspondence; the outer parts-array/weighted-sum join; fission/powers candidate adoption or original-source equivalence and fresh frozen parent/runtime pins. The generic Dot/field/c0 callbacks remain explicit here. The previous actual ClaimParser field/c0 can instantiate the latter; this packet does not claim the frozen full cached-claim function or100-bit soundness.
