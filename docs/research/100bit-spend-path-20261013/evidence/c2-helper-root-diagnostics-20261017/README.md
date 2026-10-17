# Rejected helper-only C2 extraction diagnostics

Both helper-only roots have valid Charon LLBC and fail Aeneas. There are zero
accepted helper cones, zero new proof results and zero production changes.
Neither source relocation qualifies a production extraction refactor on this
evidence. All original inputs and failed logs are retained.

| Exact target | Charon exit / wall / RSS KiB | Aeneas exit / wall / RSS KiB | Swap |
|---|---|---|---:|
| `crate::prover::copy_c2_columns` | 0 /0.402191 s /182360 | 2 /0.401390 s /67760 | 0 |
| `crate::host_commitment::encode_and_retain_lanes` | 0 /0.403974 s /193600 | 2 /0.603774 s /93808 | 0 |

Each receipt includes the exact command, tool hashes, source revision, input
pins, wall time, RSS, swap and aggregate reservation. Every scope is capped at
MemoryHigh6GiB/MemoryMax8GiB/MemorySwapMax0; aggregate recorded reservations
remain below55GiB. These were compiler lowering attempts, not Lean results;
`#print axioms` is not applicable. No Lean, SBF, native replay or runtime harness
was invoked.

The copy helper uses the exact previous diagnostic `lib.rs` bytes
`2abc3d05d4f9f01055d09dde90e7e297b9e49c44d10c1607c7b6e5e0c9f1d9d1`;
only the extraction root/namespace and diagnostic metadata change. It moves the
production loop unchanged apart from `self.messages`→`messages`. Aeneas now
fails at the helper itself (`lib.rs:218:0–218:155`,
`SymbolicToPureAbs.ml:1313`), excluding the Backend carrier as a necessary cause
of this reduced failure. It does not establish the ultimate compiler cause.

The retained-lanes helper moves exactly `host_commitment.rs:168–193` at
`5a28a4b4896aba8b07bff11c47d4683dea3c80cf`, prefix SHA256
`71dd73a722e833dae047d10870a94f03573d63a1b85608bb55b8c4e18427ecdd`.
The helper takes owned `lanes` and returns `(lanes,words,saved)`, so the reserves,
field checks, variant coefficient calls, encoder calls and pushes remain
byte-identical. Its caller replacement is confined to the isolated kit. Aeneas
fails at `InterpAbs.ml:191`, span `lib.rs:1:0–299:5`. The old encoder boundary's
`CodeField`→`Copy` signature weakening remains explicitly diagnostic; neither an
encoder body nor an encoder result is invented or accepted.

The runner source base remains `deb68369ba3ad7cc6706dc24b6503fac1cbe942b`.
Diagnostic metadata rechecks the relevant exact production fragment at5a28;
the actual helper did not exist in production at either revision. Deterministic
`prepare-helper-root.py` and `prepare-retained-helper.py` support `--check`.

No viable narrow production change is demonstrated by this checkpoint. The
smallest retained copy-helper LLBC/log is a concrete compiler-bug input; a
source-equivalent working emission or a reviewed compiler correction is needed
before adopting a change. Further speculative source refactors are not included.
Actual Backend/build owned-witness provenance remains blocking. The independently
checked host embedding primitive and conditional core do not discharge it.
Packing, salt paths, custody, complete execution recording and checkpoints stay
separate.

Archive102members SHA256:
`9b64fe50df2f41656258a777ce5144a91a2c8858755587f6cc82fbc3b63b93b0`.
Run `check-helper-diagnostics.py` to verify the archived failures without a build.
