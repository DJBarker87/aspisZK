# Six resumed unstubbed Kani invocations

Names were listed in resume5-kani-plan.txt before charging. All six new
variant/component splits executed the actual dynamic mappers with no stubs,
unwind33 and unwinding assertions. All six timed out; no equality or checked
ROW counterexample is credited. Actual compiler fingerprint retains opt-level=3,
mir-opt-level=4 and MIR inlining. One 6G/8G/swap0/tasks64 scope at a time.

GNU time RSS below is the reported timeout-process resource statistic; abrupt
termination does not aggregate all CBMC descendants. Cgroup memory.peak is the
additional full-scope memory measurement. Manual /proc VmHWM samples are lower
bounds and are not promoted to an exact aggregate peak RSS. All swaps were zero.
#print axioms: N/A for Rust/Kani. Full targets, commands, source pins, revisions
and limits are retained in each run's receipt.json and resume5-kani-invocations.jsonl.

| Harness suffix | Exit | Wall seconds | GNU time RSS KiB | Cgroup peak bytes | Swap | Source revision |
| --- | --- | --- | --- | --- | --- | --- |
| pv_srcid5_transfer_fields | 124 | 180.007311 | 15268 | 2797080576 | 0 | 639a67e175 |
| pv_srcid5_transfer_path | 124 | 180.007601 | 15284 | 2671595520 | 0 | 639a67e175 |
| pv_srcid5_transfer_public | 124 | 180.008146 | 15472 | 2489774080 | 0 | 639a67e175 |
| pv_srcid5_withdrawal_fields | 124 | 180.008123 | 15300 | 2463100928 | 0 | 639a67e175 |
| pv_srcid5_withdrawal_path | 124 | 180.007805 | 15128 | 2379444224 | 0 | 203355b9b9 |
| pv_srcid5_withdrawal_public | 124 | 180.007604 | 15300 | 2533957632 | 0 | 203355b9b9 |
