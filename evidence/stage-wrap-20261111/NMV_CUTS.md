# Source-ordered cuts and expected sizes

Frozen r1_pool_adapter_owned.rs; original complete body retained in NMV_FROZEN_OWNED.rs.txt. All cuts call ACTUAL frozen functions. Logging is in harness-local records reached through original arguments; no writable statics/function-pointer observer.

| Function | Source cuts | Native shape / expected budget |
|---|---|---|
| snapshot 29–43 | try_borrow_data; len; admitted-length disjunction; to_vec; guard Drop; metadata projection | one account, small 0–4 byte backing, arbitrary metadata/two length constants, 4 branches; ~12 checks including reply/argument/footprint controls |
| stage2 463–481 | count/magic gate; set_return_data(empty); seven snapshot calls; Clock::get; stage2_owned full Result | seven small accounts, no content materialization, SDK/std logged laws; return/reject/clock/snapshot failures; ~22 checks with three controls |
| stage1 447–461 | instruction/count gate; three snapshots; stage1_owned full Result<Vec>; exclusive borrow; length gate/copy; Drop | three small accounts; arbitrary child error and small returned checkpoint; no field arithmetic; ~24 checks with three controls and exact KMX copy control |

The child abort arm carries only its ordered prefix, no fabricated post-abort heap/cleanup. Snapshot borrow failure duplicates the SAME ProgramError into both length/bytes fields; it does not early-return from the parent. Byte to_vec/copy laws are Lean statements for arbitrary lengths; no finite small-buffer run is claimed as a 57607/1768 content proof. Extra two Kani slots reserved for isolation.
