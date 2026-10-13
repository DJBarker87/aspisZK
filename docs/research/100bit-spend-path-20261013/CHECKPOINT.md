# Research checkpoint — 13 October 2026

Goal: a transparent, trusted-setup-free private spend with at least 100 bits
of non-work-normalized soundness in at most two verification/settlement
transactions. Proof uploads are outside the requested transaction count.

This checkpoint is **not a secure-spend release**. It preserves the R1 S2
candidate, optimizations, actual Pool lifecycle adapter, V0 runtime harness,
proof/rank experiments, focused Lean lemmas, and successful and failed NUC
evidence. No live programs were deployed or funds moved. Runtime keys remain
retained securely on the NUC and are excluded from this commit.

Measured adapter-v2 ordinary V0 cases:

| Case | First verification CU | Finish and settlement CU | Terminal bytes |
| --- | ---: | ---: | ---: |
| Transfer, 13 pairs | 1,342,707 | 1,374,664 | 879 |
| Withdrawal, 13 pairs | 1,341,346 | 1,390,957 | 1,044 |

Both use a 1.4M CU limit and the 1,232-byte V0 ceiling. Lifecycle protections,
proof tampering, wrong release, stale lane, replay, and injected token-CPI
rollback were exercised. The v2 255-pair history-page rollover exceeds the
compute limit. The authenticated-parser optimization passes its focused
native equivalence and mutation gate. An initial v3 SBF build omitted the
pool-adapter feature; its failed lifecycle run is preserved and explicitly
excluded as adapter evidence. A corrected v3b build/run is the next gate.

The proposed error ledger's largest coefficient is approximately 2^-105.136,
with no grinding/work credit and with an explicit Qtot multiplier in the FS
target. `security_ledger.py` checks only the rational arithmetic. The actual
R1 source, extraction and FS composition have not yet been fully proved.

The preferred mathematical route reuses the existing decoder by repeated
lifting for the second fold, uses a joint list of at most 100 candidates
instead of an OOD uniqueness assumption, and keeps gamma and folding
challenges in WideExact. Only final residual batching uses QM31.

For privacy, two-pad compensation repairs the old gamma-in-K experiment's
field mismatch. The actual proof passes the proposed raw/silent rank checks.
An efficient simulator, exact payload correspondence, commitment hiding,
and ROM/abort analysis are still required. All cost proofs in this checkpoint
use deterministic fixture entropy. A default-off salted-leaf and secure
entropy experiment is planned but deliberately excluded from this checkpoint.

Start with these documents:

- `SECURITY-PATH.md`: architecture and remaining security obligations.
- `SECOND-FOLD-LIFT.md`: reuse of the existing matched decoder.
- `TWO-ROUND-BINDING.md`: finite-candidate round-polynomial argument.
- `PRIVACY-RANK-PATH.md`: actual-field construction and simulator obligations.
- `RESULTS-FIT.md`: verifier optimization measurements (pre-Pool).
- `evidence/pool-v0/README.md` and `evidence/pool-v2/README.md`: Pool runtime results.
- `evidence/authenticated-tx2-gate-20261013/`: strict/authenticated comparison.

The base revision is 7742957648c33cf045eb6a672e7c7cc796b61087; work is isolated
on branch codex/100bit-spend-path-20261013. Evidence receipts preserve exact
source/artifact hashes, command, exit status, time, RSS and swap. Focused Lean
receipts include axiom audits. No package-wide Lean replay was claimed.
