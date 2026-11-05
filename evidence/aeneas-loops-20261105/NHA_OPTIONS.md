# NHA non-invasive routes — in progress

All routes retain the exact pinned binary. No shared tool or frozen shipped source is edited.

## Option inventory and tested settings

Pinned help is committed as NHA_aeneas_help.txt and NHA_charon_cargo_help.txt. Aeneas exposes -strict-joins, -eval-drops, -loops-to-rec and -loops-no-rec; there is no exposed switch to disable marker invariants or repair abstraction identity. Source inspection shows the loop-to-rec/no-rec settings operate in PureMicroPassesLoops, AFTER the failing symbolic interpreter. They are not an alternate symbolic loop algorithm. Disabling assertions or swallowing a failed join is not a valid option.

| Shape | Retained input default | strict joins + loops-no-rec | eval-drops + loops-to-rec |
|---|---|---|---|
| NGA field reference (not actual frozen body) | E001, exit2, marker assertion2731 | E004, exit2, same assertion | Not allocated; actual frozen body reproduction takes this slot |
| Actual queries | E002, exit2, Map.find1991 | E005, exit2, same Map.find | E008, exit2, same Map.find |
| Actual prepared_claim | E003, exit2, Map.find1991 | E006, exit2, same Map.find | E009, exit2, same Map.find |

Exact commands/metrics are in each receipt. No timeout, memory kill, or unchanged retry occurred.

## Charon-only options / attributes

The pinned Charon help offers built/promoted/elaborated/optimized MIR, opacity/include selection, and --start-from-attribute (root selection). No documented option outlines a Rust loop or selectively changes borrow abstraction joining. ULLBC is not the structured input needed by Aeneas. The present aeneas preset already performs loop reconstruction and index/operation conversion. Switching MIR can change the extraction interface and is not equivalent to a join fix. No shipped attributes are allowed. --start-from-attribute only selects roots already annotated, so cannot create the missing helper without a source change. Scratch roots use command-line --start-from; source attributes are unnecessary. No unrecorded attribute experiment is claimed.

## Outlining specification

NHA_prepare_outline.py reconstructs private frozen dependencies from Git4bb3b3f5 and records every input hash in NHA_SCRATCH_INPUTS.json. Only the scratch workspace manifest (reduced members), two module registrations, and NHA_ modules differ. Original function bodies are preserved byte-for-byte, with wrapper names/visibility changed; original .rs.txt cuts are committed. The OUTLINED copies are deliberately different, and never described as byte-identical frozen functions.

Field: preserve exact cache prelude; lift the channel loop into NHA_channels; outer component loop calls it and threads sums. Actual frozen original is separately extracted to correct NHA-F1.

Queries: preserve QueryScan, scan, finish, query_words and block_rank helper bodies; move the eight-block loop into NHA_blocks, returning (scan,state) before the original fallible finish. There is no nested loop syntactically in queries_from_pairs: its inner word loop is already in QueryScan::scan. This is caller/helper fission, not an invented inner loop.

Claim: lift the29-lane dot loop into NHA_dot with exact scalar selection/push/map_err/finish, returning Result<E,Error>. Also lift the final7-term weighted sum and ordered trace calls into NHA_sum. The earlier read-only S1-CACHED-CLAIM-FISSION-PROGRESS-20261020.md records that inner-only outlining still failed on the final sum; hence the new attempt tests both fissions. It is not a repeated known failing inner-only shape.

Any successful outlined emission requires the ruling(ah) actual frozen function/reference contract, exact modifies, matched control and reviewed transcription. There is no emitted original-body theorem to which Lean can equate the outlined copy. No equality or native bridge is claimed here. Kani is forbidden by this job's0 budget.
