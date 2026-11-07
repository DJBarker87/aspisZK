# RSL check record

Target not yet established. This record covers specifications only. No proof that any frozen function satisfies its RowSpec was attempted.

## What compiled locally

All 21 modules compile on the development machine (Apple arm64, macOS):
- `RSL_Base`, `RSL_Pool` and `RSL_Verifier`;
- the 17 row modules (TX2:217, 234, 233, 242, 241, 240, 221, 213; TX1:136, 137, 087, 094, 328, 345, 344, 333, 330);
- `RSL_Audit`.

**How it was run.** Toolchain leanprover/lean4:v4.31.0 (commit 68218e87, the Aeneas pin), core Lean only, with no Mathlib, Aeneas or repository imports. The lake workspace is this directory, with `lakefile.toml` and `lean-toolchain`; `.lake/` is not committed.

Command, one file at a time in dependency order, from `rsl_compile.sh`:

    lake env lean -o .lake/build/lib/lean/<M>.olean <M>.lean

**Final clean replay.** The replay started at 2026-11-07T07:52:48Z, after all `.olean` files were deleted. It ran from the worktree at commit 8e8929267ee plus the uncommitted TX1:344/333/330 and audit modules, which are committed with this file.

| Measure | Result |
|---|---|
| Exit status | 0 for every file |
| Total wall time | 6.26 s |
| Peak RSS of any single file | 728,465,408 bytes (RSL_TX2_217, kernel `decide` on the 768-byte witness) |
| Swaps | 0 |
| Cgroup | none. These are focused single-file jobs far below 8 GiB, so no build host was used |

The per-file exit, wall, RSS and swap figures are in RSL_COMPILE_FINAL.tsv. RSL_COMPILE_LOG.tsv keeps every earlier attempt, including the failed elaborations that were repaired by changes to the source.

**Axioms.** RSL_AUDIT_OUTPUT.txt holds the `#print axioms` output for every rejection theorem. Each depends only on `propext` and/or `Quot.sound`. There is no `sorryAx`, no `Classical.choice` and no `native_decide`/`Lean.ofReduceBool`. The two warnings in that output are unused-simp-argument lints.

## Rejection of trivial implementations (compiled)

Every theorem below is a compiled Lean `theorem`.

| Row | Theorem(s) | What is rejected |
|---|---|---|
| 217 | `rejects_constErr`, `rejects_constAbort` | every constant Err (by a concrete well-formed 768-byte lane image); constant abort |
| 234 | `rejects_constErr`, `rejects_constAbort` | needs only that the CLOSED policy validator accepts the audit policy |
| 233 | `rejects_constErr`, `rejects_constAbort` | NotEnoughAccountKeys vs InvalidArgument |
| 242 | `rejects_constErr`, `rejects_constAbort` | needs a request the CLOSED decoder accepts |
| 241 | `rejects_constErr`, `rejects_constAbort` | same request hypothesis plus its magic prefix |
| 240 | `rejects_silentErr`, `rejects_constAbort` | every event-free Err with any post-state |
| 221 / 333 | `rejects_silentErr` | for every stage1 law |
| 213 / 330 | `rejects_silentErr`, `rejects_constAbort` | as for 240 |
| 136 / 137 | `rejects_constErr` | conditional on the CLOSED semantic_rounds or parse law having a silent Err-only argument |
| 087 | `rejects_wrong_g` | the `&mut g` frame is pinned on early Err arms |
| 094 | `rejects_constErr` | Parse vs Allocation |
| 328 | `rejects_silent` | every event-free outcome at k ≠ 10 |
| 345 | `rejects_constErr`, `rejects_constAbort` | wrong route vs duplicate keys |
| 344 | `rejects_silentErr`, `rejects_constAbort` | as for 240 |

## What remains unchecked

1. **Correspondence to the canonical Lean objects.** The package is self-contained, and nothing was imported from the repository forest. The following are therefore unchecked here:
   - that each `PoolLib`/`VLib`/`V2Lib`/`S1Lib`/`DeployedIds`/`PreparedNew` field equals the model in the named CLOSED root, and that each `Child.dom` is exactly that child's ledger clause set (RSL_LEDGER_CLAUSES.json lists the clauses);
   - that the RSL SDK model (`Cell`, `acquire`, `release`, `snapshot`) is the NLF_RefCell / NLF_SdkModel / NLF_ParentModel transcription it claims to be;
   - the representation bridge from Aeneas carriers (`Slice U8`, `Std.Result`, structs) and from NMN_064.RowSpec's `End`/chronology to `Bytes`/`Obs`/`Event`;
   - that `V2Lib.Root0` is NLP_InputDomain.Root0 on byte carriers.

   The worker or the next ledger gate proves these as definitional or refinement lemmas on the host, inside the combined import.
2. **Line-by-line review of each `Ref` against the frozen body.** This was done by reading only. It is the ReviewedTranscription item for each row and must be re-reviewed at the gate.
3. **Two frozen constants** were transcribed from the source rather than from a compiled evaluation: `checkpoint_size(S2) = 1768` and `STATEMENT_BYTES = 1880`. They are consistent with NMN_064.Domain.
4. **Satisfiability of the domains at the actual callers.** In particular the entry-level Root0 clause (RSL_INDEX.md item 1) and the publicDom derivation at TX1:345 (item 3).
5. **No host, Kani, extraction or combined-import run was made.** No emitted body was inspected.
