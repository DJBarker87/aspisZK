# Frozen native wide samplers equal the checked owned reference

The source-value gap identified in R4-TRANSPORT-20261021.md is now narrowed
by whole native function comparisons, beyond the earlier dataflow/range gates.
Source freeze4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; no production code changed.

1. For EVERY typed32-byte block, actual optimized low_base_p_digits returns
   exactly the owned indexed reference's complete8u32 digits AND remainingu32
   quotient. No arithmetic/result/iterator callee is stubbed.
2. For EVERY typed32-byte block, actual ordinary_sample and gamma_sample
   each return all8 native words equal to the corresponding owned indexed
   reference. The complete native core WideExact/CM31/M31 types and constructors
   are used on BOTH native sides; no u64/simplified field carrier substitutes
   for the source result.

The reference bodies are exact complete selected functions from
post25-indexed-addsmall-source-model-20261020/extraction/candidate-input/lib.rs,
whose indexed source/math proofs already exist. The low-base helper reference
comes from post25-indexed-sampler-candidate-20261019/sources/sampler.rs and uses
the unchanged actual qm31_div_pass. The reference constructor WideExact.new
and canonical_qm31 bodies are literally the current native bodies modulo
whitespace. The imports are bound to actual core types rather than copying
simplified type definitions into the native comparison. The existing nominal
Lean carrier maps/source-reference proofs retain their own pins; this is not
a claim of coherent whole-release replay.

Before: scalar/address/frame components and generic Lean loop composition
left mutable original helper/reference value equality open. After: both public
native wide samplers and the complete low-base helper have whole all-input
value equality checks, including source bounds/debug assertions and loop
exhaustion under the default Kani checking model. Source/std initialization,
allocator/runtime interpretation and the final native/math/caller/oracle/release
composition are not silently inferred. No custom Lean axiom is introduced.

The decisive change was solver choice, not RAM or altered source:

| Target | Solver | Exit / checks / covers | Wall s | Process RSS KiB | Swap |
|---|---|---|---:|---:|---:|
| Exact low-base helper |Z3 4.15.4|0 /0of320failed /1of1|4.627940985|174884|0|
| Complete ordinary |Z3 4.15.4|0 /0of353failed /1of1|5.433170985|177128|0|
| Complete gamma |Z3 4.15.4|0 /0of430failed /1of1|19.460995113|191400|0|

Verification-only times were3.838056s/4.5628433s/18.62437s respectively.
Each has12GiB max/11GiB high/Swap0, fresh admission and zero pressure/OOM events.
The helper CaDiCaL predecessor timed out500s at about1.4GiB cgroup peak. It
remains excluded. The Z3 attempt reuses the exact source/GOTO/focused compile,
checking all original tool pins and adding the private already-warm Z3 binary/
libraries/metadata hashes and PATH. The bounded private tool was reused without
installing or modifying system software; no solver binary is exported.

Exact source/tool/import/revision/commands/status/wall/RSS/swap records and
source-only snapshots are in sampler-value-history-v1 and sampler-public-history-v1.
Read-only audits pass30 and34pins. #print axioms is N/A for Kani; no new Lean
axiom or resource-option override is used. Local smallest changed-target
codegen passed before each new native job. Initial helper runner name-parsing
failure occurred before compiler launch and is retained; the unused parser
was removed. A compile-only inherited kind label is corrected in accompanying
metadata rather than rewriting old receipts.

Remaining work includes consuming the fixed owned reference/source math pins
in the enclosing caller join, actual query-pair source/model binding, the four
S5-owned dot/arithmetic bindings, concrete SDK/first-stage/std/allocator/runtime,
ordered event/oracle transport and coherent final release/artifact evidence.
Whole S1/S6 and <=2^-100 per-attempt soundness remain NOT ESTABLISHED. No grinding
or work-normalization credit or new source adoption is requested here.
