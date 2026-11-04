# PV_STX work in progress

Branch codex/pv-stx-20261104; base fd4a644fd414079022f8781c14a6683b41504ab7.
No privacy premise has been removed. The target is not yet established.

The accepted ae1-2 binary remains SHA-256
fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68.
The retained pv-cx2 identity tests are copied verbatim under ae1/, with their
original branch provenance. This job has not rebuilt or changed the translator.

Source inspection finds no state-threading CLI option. The state-error comments
are historical: FunsAnalysis.stateful is not propagated to pure fun_effect_info;
SymbolicToPureTypes.compute_raw_fun_effect_info retains can_fail/can_diverge/is_rec
only, and mk_output_ty_from_effect_info wraps output in Result only.
The full inspected OCaml files and whole-src search output are retained.
All inspected file hashes match pv-cx2's accepted source recovery record.
The verbatim binary help run N91800 is waiting outside a scope on the quiet
window ending 2026-11-04T01:37:50Z (until 1793756270). No bypass was used.
Route B is being prepared; the help result will complete the route decision.

PV_STX_Code, Machine, Fixed, PrefixLaws and Entropy are DRAFTS, not yet compiled.
They introduce syntax and a continuation machine; the entropy lift covers six
actual extracted declarations and five opaque call kinds, not a whole prover
helper. It has a reproducible syntax generator and fixed-dictionary erasure
statements. Finite ordinary Result nodes still need native effect classification.
No source_entry_world declaration or five deployed projection equations exist.
No claim of native fidelity or premise discharge is made by the syntax draft.

One source transition is evaluated at the current world. A returned value resumes
its saved continuation at the reply's post-world. Failure/div/fault stop there,
retaining events and post-world. Pending retains the request and continuation;
external pending resumption still needs a native driver whose internal progress
is represented in the world, not a restarted whole-helper Result call.
