# Native leaf checks and excluded shapes

10/10 Kani runs, all optimized (dev opt-level3, debug0, overflow checks), one
compiler job and one admitted capped scope per run. Caps 6G/8G/Swap0/Tasks64.
Kani axioms: N/A. K001..K010 receipts pin exact command, harness, source hashes,
revision, dependency boundary, timeout, exit, wall, RSS, swaps and cgroup.

| Run | Domain / actual native calls | Result |
|---|---|---|
| K001/K002 | Sparse WideExact coordinate0/1 in {0,1}, arbitrary canonical base-field scalar; source EbyKDot single push versus native mul_qm31 | PASS; nonzero cover reached |
| K003/K004 | Zero/one wide first addend, arbitrary canonical base-field scalar; second zero addend frame | PASS; nonzero scalar cover reached |
| K005 | Actual public verifier::checkpoint, S2/64 zero weights, arbitrary first query u32, concrete other fields and BoundaryDigest | CBMC 90s TIMEOUT (95.656466s enclosing run); no result, no unchanged retry |
| K006 | Source checkpoint query-loop serialization expression: arbitrary u32 and arbitrary 8-byte vector prefix, native to_le_bytes/extend_from_slice and prefix frame | PASS; maximal u32 cover reached |
| K007 | Native QM31.write_le_bytes/from_le_bytes, four arbitrary canonical limbs | PASS; all four exact byte chunks plus roundtrip |
| K008 | Native private WideExact.from_limbs/to_le_bytes/from_le_bytes, eight arbitrary canonical limbs | PASS; all eight exact chunks plus roundtrip |
| K009 | Checkpoint header expression: arbitrary usize next, exact low-byte truncation and unchanged magic prefix | PASS; next>255 cover reached |
| K010 | Actual checkpoint_size for S1/S2/D; fixed prefix744 and payload/weight/checksum layout | PASS; all variants covered |

After K005, the five remaining checkpoint harnesses were replaced by the named
serialization/layout leaves. Original K001..K005 and replacement K006..K010
source snapshots are retained separately. No timed-out whole-checkpoint shape
was rerun, no timeout/cap increased, no source extraction ran. This does not
establish native whole prepared_claim/checkpoint P6, chronological digest
attempts, allocator errors, saved physical bytes or an actual-top instance.

XRl_native_toolchain_pins.json compares six actual native source files and
Cargo.lock against the worktree and immutable release revision
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; every hash matches. The unchanged
S2W runners are also hash-checked against the coherent workspace.

Lean L097 whole-checkpoint model size projection hit the default 200000
heartbeat limit after23.795s (not a memory kill). Its source and full errors are
retained. It is not retried. L098 proves only the isolated final check/conversion
fragment on an already supplied byte list, avoiding whole-body normalization.
The whole checkpoint projection and dependent TX1 size composition are retained
as unaccepted *_CANDIDATE.lean.txt, never imported. XRl_CheckpointBytes gives the
separate checked 4/16/32-byte model encoding size laws.
