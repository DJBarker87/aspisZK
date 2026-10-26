# Unstubbed harness inventory to request

The first six names are source-declared in cfg(kani) harness modules. They must be
confirmed from successful Kani codegen metadata before charging verification:

- records_proofs::pv_srcid3::pv_srcid3_full_mapper — all twenty record fields;
- records_proofs::pv_srcid3::pv_srcid3_mapper_values — scalar projection;
- records_proofs::pv_srcid3::pv_srcid3_mapper_path — direction and sibling projection;
- records_proofs::pv_srcid3::pv_srcid3_mapper_digests — key/owner/pair digest projection;
- records_proofs::pv_srcid3::pv_srcid3_mapper_public — frontier and actual roots;
- builder_reference::pv_srcid3_external_owned_unstubbed — complete external callback.

No stubs or verified_stubs are allowed. Unwinding assertions remain enabled.
The mapper bound is 33; external bound 17. Inputs are arbitrary raw words;
assume statements only bound the projection's array indices. Time is expected
in proof compilation and CBMC simplification/checking, particularly two actual
empty-root computations. No debug arithmetic release gate is launched.
One own scope at a time; fixed quiet hold until 18:15; fresh host reservation.
Stop the verification queue on the first configuration failure. A failed
full-mapper job must be decomposed, not retried unchanged with more resources.
Inventory invocations also count conservatively against the 12 Kani budget.

Additional source validator leaves (to list in metadata before verification):
`pv_srcid3_common_values`, `pv_srcid3_common_sibling`, and
`pv_srcid3_common_pair_words`. These call the shipped validate_common with
matching context/fresh spent set, arbitrary raw pair inputs, and unwind 21.
Success implies the exact primitive range/canonicality facts. They do not
claim a full forest run, output-bound check, or mapper equivalence.
