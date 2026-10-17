# Verify/query refactor native evidence

All accepted targets exited 0 with zero swap under MemoryHigh=6GiB,
MemoryMax=8GiB, MemorySwapMax=0. Exact commands, revisions, reservations,
wall time, RSS, source snapshots and logs are retained in `native-evidence.tar.gz`.
Archive SHA256: `5c192d1d15fea5207c1f8bb386708b68654ae121dca00eef85792731c2821427`.

| Accepted target | Cases | Wall seconds | Peak RSS KiB | Revision |
|---|---:|---:|---:|---|
| verify-real-s2-default | 112 | 4.767929340 | 248192 | a555c852664c80000942f0c911e16719a5493625 |
| verify-real-s2-detail | 112 | 3.796710474 | 246860 | a555c852664c80000942f0c911e16719a5493625 |
| query-migration-102 | 102 | 5.044606174 | 261744 | 5a28a4b4896aba8b07bff11c47d4683dea3c80cf |

The verify tests compare the old lead body with the candidate using the saved
S2 proof and actual parser, transcript, field operations, arithmetic checks and
terminal code. Each observer mode covers success and 55 failure points: Prefix
parse, public_transcript, begin, the moved row14 initializer, and each lookup,
decode, boundary and semantic step in rows15–24. Both detailed-trace feature
settings are covered. Complete outputs, errors, Digest32 calls, trace marks and
observer phases agree. Test-only interface failures are not asserted to be
reachable from unmodified production inputs.

The query test compares actual old/new query bodies in saved-S2 and synthetic
S1/two-fold contexts. It covers each of 16 digest positions with a caught abort
and a one-bit altered answer, queries_from_pairs failure, and success: 34 cases
per context. Digest32 is infallible; caught digest aborts are not ProgramErrors.
Synthetic contexts are not claimed to be valid saved proofs. All 22 trace values,
decoder arguments/results and carried states agree. The saved-S2 context and
17 calls are checked against the retained 583-call ordered counter trace.

The query target is re-pinned to a555 by byte equality of its entire production
file, transcript.rs, and all 530 other production files; only r1_semantic.rs
changed after its run. Its unchanged gate was not repeated. The earlier 5a28
verify runs remain in the archive as superseded history, excluded from acceptance.

Reproduce the read/hash-only audit (no builds):

```sh
python3 tools/r1-verify-migration-kit/check-evidence.py \
  docs/research/100bit-spend-path-20261013/evidence/verify-query-native-20261017/native-evidence.tar.gz \
  --sha256 5c192d1d15fea5207c1f8bb386708b68654ae121dca00eef85792731c2821427
```

`check.json` records that audit's exact invocation, exit, time, RSS, swap and
revision. #print axioms is N/A for these Rust and read/hash-only results.
No SBF build or readonly runtime harness ran.
