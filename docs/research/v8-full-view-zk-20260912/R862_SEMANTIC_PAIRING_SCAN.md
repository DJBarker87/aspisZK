# R862 fixed-witness semantic pairing scan

This is a bounded, optimized Rust field-model diagnostic. It records a fixed-witness candidate in the 699-direction search. It does not prove a 223-row minor, source-to-model correspondence, challenge legality, privacy, or security.

The exact computation used `z=[1,1,2,3,4,2,2,3,0,2]`, `alpha=7`, `kappa=5`, chord parameters `[7,5,-5]`, `half=1073741824`, `quarter=536870912`, and `M=2147483647`. For every pair `d=22..254`, `s=1..3`, the scan formed `q=pair(d,s,7)-pair(0,s,7)`. It retained the earlier 222-vector observations and their checks (first-fold zero, four zero top entries, inactive balance, and transport round trip), then appended the fixed semantic pairing

```text
sum(i=0..270) coins[i] * m[transport.order[128 + 3*i]]
```

using the frozen `coin_weights_into(z, coins)` and the same inverse mask as the old observations.

The saved TSV has all 699 candidates, each with its old 222 QM31 values and the appended QM31 scalar. The scan summary reports 223 candidates whose old 222 values are all zero while the appended scalar is nonzero. The first is `(d,s)=(96,1)`, with scalar `(1610612604,0,0,0)`. The TSV and summary are retained byte-for-byte in the evidence directory.

The source/module and run artifacts are in [the R862 evidence bundle](evidence/r862-semantic-pairing-scan/). The bundle includes the exact staged Rust sources, Cargo manifest and lockfile, runner, source diff, launch command, complete logs and both systemd terminal records, the full TSV, the selected R117 flags, and source pins. `SHA256SUMS.txt` hashes every file in that bundle except the manifest itself.

The frozen selected source tree was `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`, recorded at source revision `6677d5f1310ff7373301fbd79f186278f772e68a` in the campaign source map. That exported tree has no `.git` metadata; the revision is therefore a recorded source pin, not a revision recovered from that directory. This packaging worktree was at `3d9a916925da0d7f4fbdb0e8081ce66df18a4a21`. The selected `performance.rs` snapshot is SHA-256 `4c575d4d1004bf39b0bb1f8069495e315e63a7ec9f423a60ec93f3487f4eb8b5`; the selected `r16_basis_transport.rs` snapshot is `678c64e08e7d14bb6bc160042f0ee01cb39e260748ec1ac95cce008969d586ae`. The exact R117 rustflags file is included and hashes to `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`.

The successful run used NUC systemd unit `aspis-r862-semantic-pairing-20261005-b.service`, invocation `0fd20df9a80549aa931b92ffc504c125`, with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. It ran offline, locked, optimized Cargo release mode with one job, one codegen unit, and overflow checks enabled under the frozen R117 flags. The exact launch command and full build/run output are archived. Exit status was 0; elapsed wall time was 25.77 seconds; peak RSS was 599,024 KiB; swap was 0.

The first launch record is also preserved. That attempt exited 127 after 6 ms because `systemd-run` lacked `--working-directory`; the probe script did not run. The corrected launch changed only that option. No verifier CU benchmark, regression suite, prior 69-case low-constancy check, old 222-rank computation, or 223-row minor calculation was run as part of this diagnostic. Rust diagnostics have no Lean `#print axioms` output (not applicable).

The result is only a fixed algebraic witness-search observation. No source roots were evaluated by this runtime scan, the fixed tuple is not established as an accepted sampled prefix, and the ordinary optimized/reference equivalence for this new pairing was not proved. The next formal obligation is a universal 223-dimensional joint minor/source-normalization argument; the source binding, legal-prefix distribution, causal-oracle accounting, simulator, and end-to-end privacy/security arguments remain open.
