Exact-chunk coverage for successful record payloads, Lean4.31

RecordPayloadPartition.table_size_mod proves every admitted table size is
a multiple of32. payload_length_mod derives the payload fact from actual
extracted parse_record success. Generic toChunksExact lemmas prove partition,
exact chunk size and remainder length modulo the chunk size. Therefore
successful_payload_covered proves empty remainder and exact flattening back
to the entire payload, without assuming divisibility. Field validation is
not asserted here; the validator-loop theorem composes separately.

Final partition-b exits0 in24.840s; sampled process-group peak2562496KiB;
process maximum RSS2134867968bytes and process swaps0. All7 axioms reports
contain only propext,Classical.choice,Quot.sound. Global system swap increased
from12066.62MiB to12556.06MiB during the check; zero process swaps does not
mean zero system swap. One unused-simp warning remains; no replay to remove it.

Attempt-a hit a simplifier cycle from explicitly unfolding UScalar.val and
BitVec.toNat in the table lemma. The correction uses constructor injection
and small concrete arithmetic; limits were not raised. Its sorryAx reports
are retained as rejected evidence, while final source/logs are separately pinned.

Each command was lake env lean through the retained cache wrapper with
-M3500, a sampled4GiB group stop and180s timeout. This is not a hard cgroup.
Exact commands/source/object pins/runtime libraries/revisions and swap
observations are in the receipts. Imported objects are retained cache evidence,
not a fresh backend or historical reproducible build. No host/cold/full build.
The final source is independently equal to the live proposal file.
