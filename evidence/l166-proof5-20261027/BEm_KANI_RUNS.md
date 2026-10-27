# Kani inventory:15 local passes,5 excluded timeouts

20/20 proof runs used. No stubs or unverified contracts. Each pass requires exactly one VERIFICATION SUCCESSFUL and no VERIFICATION FAILED. All five timeouts have raw exit0 and misleading manual summaries, so raw exit/manual summaries are not admission evidence. No whole-body certificate is claimed. All swaps0; caps6G/8G/Swap0/Tasks64. Full source, revision/hash, bounds, command, exit and logs are in per-run receipts.

|Run|Exact harness|Disposition|Wall s|Process RSS KiB|Cgroup peak bytes|
|---|---|---|---:|---:|---:|
|BEm_K01|BEm_reference::physical_step_c2|VERIFIED local cut|27.656690|1100292|1142538240|
|BEm_K02|BEm_reference::physical_step_folded|VERIFIED local cut|29.883819|1087344|1129132032|
|BEm_K03|BEm_reference::physical_step_c1|VERIFIED local cut|42.777371|1580228|1635205120|
|BEm_K04|BEm_reference::physical_loop_c2_0|EXCLUDED timeout|181.957076|6563892|6737440768|
|BEm_K05|BEm_reference::parent_owned_record|VERIFIED local cut|5.727755|293884|271732736|
|BEm_K06|BEm_reference::parent_pending_prefix|VERIFIED local cut|4.932922|281040|236417024|
|BEm_K07|BEm_reference::mixed_sequence_c2|VERIFIED local cut|20.225258|922804|961069056|
|BEm_K08|BEm_reference::mixed_sequence_folded|VERIFIED local cut|30.806854|911644|948817920|
|BEm_K09|BEm_reference::mixed_sequence_c1|VERIFIED local cut|30.509232|1336984|1384919040|
|BEm_K10|BEm_reference::padding_whole_slots|EXCLUDED timeout|181.780140|1898308|1960448000|
|BEm_K11|BEm_reference::repeated_query_batch0|EXCLUDED timeout|182.896910|6415024|6586200064|
|BEm_K12|BEm_reference::repeated_keys_cut|VERIFIED local cut|102.499715|2674604|2752151552|
|BEm_K13|BEm_reference::prefixed_leaf_c2|VERIFIED local cut|8.139415|386800|410181632|
|BEm_K14|BEm_reference::prefixed_leaf_folded|VERIFIED local cut|11.011156|386652|410075136|
|BEm_K15|BEm_reference::prefixed_leaf_c1|VERIFIED local cut|20.255082|774336|807288832|
|BEm_K16|BEm_reference::duplicate_parents_retained|VERIFIED local cut|9.864587|372736|394194944|
|BEm_K17|BEm_reference::threaded_heads_c1_c2|VERIFIED local cut|42.644912|885640|922226688|
|BEm_K18|BEm_reference::threaded_heads_c2_folded|VERIFIED local cut|100.214939|1050068|1089638400|
|BEm_K19|BEm_reference::unary_verify_full|EXCLUDED timeout|182.491456|3240248|3339173888|
|BEm_K20|BEm_reference::physical_parent_group|EXCLUDED timeout|182.711870|6539420|6712537088|

K01–03: arbitrary one-iteration Result/scratch/full owned-record coordinates, three leaf grammars; two-entry stateful reply tape and cursor<1024.
K04: n10 full leaf loop TIMEOUT; split into K01–03 plus inherited BEl/Port4B induction (concrete loop association remains open).
K05–06: binary-parent full record/coordinate grammar; real pending entry at backend entry and earlier pending-prefix retention.
K07–09: leaf→parent exact occurrence/part/byte/reply observation with two-entry stateful replies, all three grammars.
K10: up-to688-word padding scan TIMEOUT; first8-byte predicate uses inherited BEl_K12; new BEm symbolic arithmetic/traversal/cut proofs avoid concrete unrolling.
K11: restricted repeated-query whole-body TIMEOUT; overbroad global689 bound overexpands node_count. Replaced with first key/sort cut K12, not rerun.
K12: actual key/sort cut on repeated queries, BOTH ordinals and ALL three trees, arbitrary query and coordinate; exact bound13. Restricted domain, not a batch theorem.
K13–15: actual owned leaf record after one prior pending/returned entry; byte/part/old-entry preservation across each leaf grammar.
K16: two identical parent addresses retain distinct occurrences and arbitrary replies.
K17–18: first head followed by next-tree head on continuing result, same live scratch with logical count reset; all result/state/log coordinates. This is not a complete tree triple. K18 uses18-entry cyclic tape after the source-generalization; K17 uses two entries; exact snapshots retained.
K19: full18-level unary verify API/in-place observation with arbitrary index, leaf, root, nodes and18 independent replies TIMEOUT. No certificate for that scope.
K20: its first actual occupied/sibling inner hash cut with full owned records TIMEOUT. Added only cfg(kani) access wrappers in standalone evidence crate; original helper bodies remain exact. Budget spent; no claimed pass, contract stub or unchanged rerun.

For complete rejected/accepted P6 scratch induction and source accounting, reuse the predecessor receipts/modules. These local Kani results do not manufacture the complete physical carrier/recorder association or ARQ same-experiment join.
