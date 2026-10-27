# Kani receipts, resumed allocation 6

Four new exhaustive full-mapper partitions; no earlier failed harness was repeated unchanged. Each uses actual dynamic roots on both sides and compares all 20 fields. Unwind=33 with unwinding assertions, stubs=[], verified_stubs=[] in generated metadata. All 142 Rust compilation inputs match branch bytes. Actual compiler fingerprints include opt-level=3 and mir-opt-level=4. Heavy time was CBMC after compilation.

| Partition | Exit | Wall seconds | GNU-time RSS KiB | Cgroup memory peak bytes | Swaps | Revision |
| --- | --- | --- | --- | --- | --- | --- |
| pv_srcid6_transfer_first | 124 | 180.008 | 15116 | 2597871616 | 0 | ff6a78f442 |
| pv_srcid6_transfer_second | 124 | 180.007 | 15648 | 2561499136 | 0 | ff6a78f442 |
| pv_srcid6_withdrawal_first | 124 | 180.013 | 15312 | 2607497216 | 0 | ff6a78f442 |
| pv_srcid6_withdrawal_second | 124 | 180.003 | 15300 | 2444754944 | 0 | ff6a78f442 |

GNU-time RSS is for the timeout process, not aggregate solver-descendant RSS. The cgroup memory peak includes the full scope, with distinct semantics. No aggregate peak RSS is invented. No verification success and no checked ROW counterexample occurred.

All scopes ended inactive. A resource refusal before withdrawal/second try0 was uncharged, waited three minutes, and was retried as try1. Read-only owned FD scans identified no solver /tmp files; no unrelated temp file was removed. The own generated Rust cache (464,949,174 bytes) was removed only after preserving metadata, fingerprints, input pins and receipts; its filename scan found no wallet/key candidates. No wallet key was created, removed or destroyed.
