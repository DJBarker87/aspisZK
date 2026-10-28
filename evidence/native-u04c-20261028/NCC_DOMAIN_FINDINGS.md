# Domain and association gaps

These are proof-scope findings from source inspection, not new executed native
counterexamples or shipped implementation defects.

1. K025–034 constrain a live slice length through format-width + 1. The actual
registry/entry authentication callers pass account data after owner/read-only
checks, without proving those small upper bounds. ASQ8 passes its instruction
suffix to the decoder. Thus these bounded gates cannot serve as full-domain
callee bridges or justify a contract requiring those bounds. All malformed
larger-length rejection branches remain part of the native obligation. The
width check inside each decoder strongly suggests a separate symbolic length
cut, but source inspection alone is not credited as that bridge.

2. The native getter and policy contracts/checks use full typed domains and
valid references. No flags, status, slot, canonicality or successful-decoding
restriction is added. All checked callee contract preconditions are `true`.
They do not have the bounded-slice gap above.

3. The real private validator caller is below the V1 registry decoder. Proving
its contextual use of is_immutable does not identify the SDK authentication
op26 point or its record from one actual enclosing native execution. The
NBX_SOURCE_ASSOCIATION.json source map and kernel selection lemmas are reused;
they remain inspection/installation components, not the missing native parent.

4. op48/op49 include the real decoder, error mapping and Box allocation. NBX's
one-iteration/induction/read-window facts are retained without replay. They
still need association with the actual original iterator/reader, Box/error/
allocator execution and actual caller. A whole-buffer replay is forbidden and
no new unverified callee stub is introduced to manufacture these components.

Frozen source references: programs/r1-cost-probe/src/r1_pool_adapter.rs and
r1_pool_adapter_owned.rs, hashes in NCC_IMPORTS.json's imported source-association
packet and NCC_FROZEN_SOURCE_AUDIT.json. No new runtime trust, assumption,
headline/model change or cryptographic security number is proposed.
