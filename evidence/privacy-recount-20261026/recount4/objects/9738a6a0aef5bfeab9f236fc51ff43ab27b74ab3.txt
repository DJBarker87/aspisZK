# Remaining named Kani queue

Invocations1–3 are recorded separately. Before charging invocation4, the
planned queue is:

4. metadata only: `--harness pv_srcid3`, regenerate metadata after validator
   unwind changed21→33 to cover actual32-byte context arrays; no verification.
5. `pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_mapper_values`
6. `pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_mapper_path`
7. `pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_mapper_digests`
8. `pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_mapper_public`
9. `pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_common_values`
10. `pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_common_sibling`
11. `pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_common_pair_words`
12. A further isolated obligation after results1–11; name before charging.

All seven verification harnesses are new unstubbed projections, not an unchanged
rerun of the failed aggregate mapper. Formula slicing preserves safety assertions
and explicit unwinding assertions. Each gets180seconds, optimized compilation,
6G/8G/swap0/tasks64; own scopes never overlap. Refusal is not a charge and
requires a180-second wait. First configuration failure stops the Kani queue.
The source Records mapper is called in every mapper projection, including its
actual pair_empty_roots computation. A successful subset does not establish
whole-mapper equality. Root history certificates do not replace this gate.

Invocation12 is now named before charging:
`pool_v1::pair_forest_copy_builder::records_proofs::empty_roots::pv_srcid3_empty_roots_full`.
The new isolated cfg(kani)-reachable harness calls the actual pair_empty_roots
end to end and checks all168 table words, unwind33, stubs=[]; it does not invoke
or inherit the sibling checked-call-trace stub harness. Its purpose is to
isolate the pure root-helper gate from arbitrary mapper data after projection
timeouts. Source compile and verification are charged together only if admitted.
