# R0 opening-weight extraction evidence

Base worktree commit: `0dbaf0c8d576a8da71e031b89cef2c9083c67cca`.

This evidence covers the focused extraction of `AspisR0.RoundNormalization.dot`
to `R0/Dot.lean`, the exact Boolean opening-weight block to
`R0/OpeningWeights.lean`, and the arithmetic D18 bridge in
`R1D18OpeningWeights.lean`. The moved opening-weight declarations retain their
original names, namespace, bodies, and source-section typeclass context. The
D18 bridge uses the explicit point reversal corresponding to the inspected
`toR0` coordinate order; it makes no protocol-semantics or Rust-refinement
claim.

Final focused checks ran on the pinned NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` through
`./compile-one.sh`, whose recorded scope is `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, `TasksMax=128`. Final green attempts:

| Target | Attempt | Source SHA-256 | Exit | Wall time | Peak RSS | Swap |
|---|---|---|---:|---:|---:|---:|
| `R0/Dot` | `d` | `9347df933fb49a436b98e25309980ff4f8939088ad11546ae537a16885bddf2f` | 0 | 1.14 s | 2,734,640 KiB | 0 |
| `R0/OpeningWeights` | `c` | `44e2f004820cd0eb211fef5929b39cffa8bd359b4fa2455f9bad57de33a61199` | 0 | 1.23 s | 2,753,896 KiB | 0 |
| `R1D18OpeningWeights` | `e` | `69f97c6c86e58b93c71a6cc3eff79a0352e786a2abae22efc04f5f0d1dadd70d` | 0 | 1.20 s | 2,752,620 KiB | 0 |

The D18 output records `#print axioms` for all six bridge lemmas. Their only
reported axioms are `propext`, `Classical.choice`, and `Quot.sound`; no
`sorryAx` occurs. The pointwise indicator result specifies `(1 : K)` so its
codomain is unambiguous.

All earlier attempts are retained under `remote-evidence/` with their receipt,
source hash, output log, and time log. Dot attempts `a` and `b` were failed
imports/section-shape revisions; `c` compiled before restoring the exact
original section context and is superseded by `d`. OpeningWeights attempt `a`
failed because the new module had not opened `AspisR0.RoundNormalization` and
had an unclosed section; `b` compiled and `c` rechecked after Dot's final
context restoration. D18 attempt `b` exposed required original finite-field
typeclass assumptions and an indicator numeral inference issue; attempt `c`
fixed the theorem context but still exposed the indicator typing issue;
attempts `d` and `e` are green, with `e` rerun after Dot's final revision.
Attempt `b` is the first compile of the previous Field-only D18 draft and is
not green. The approved final D18 source includes the existing
`[Fintype K] [DecidableEq K] [Algebra (ZMod P) K]` context used by the source
opening weights; no checked theorem premise was weakened.

The historical dependents `R0/RoundNormalization.lean` and
`R0/OpeningDefinitions.lean` were not compiled in this task. They remain for the
root reviewer to check after the concurrent field-refactor work completes.

Final checked source hashes:

| File | SHA-256 |
|---|---|
| `R0/Dot.lean` | `9347df933fb49a436b98e25309980ff4f8939088ad11546ae537a16885bddf2f` |
| `R0/OpeningWeights.lean` | `44e2f004820cd0eb211fef5929b39cffa8bd359b4fa2455f9bad57de33a61199` |
| `R0/RoundNormalization.lean` | `af1a59d786104ba215c5c241c9ac7b32fff3c828b51456e6320522792584c0c4` |
| `R0/OpeningDefinitions.lean` | `fd3b3efc5dbcb7681dc54053a5caf7b8005f618fb7e2ad37c7c0764a6fa3da27` |
| `R1D18OpeningWeights.lean` | `69f97c6c86e58b93c71a6cc3eff79a0352e786a2abae22efc04f5f0d1dadd70d` |

`SHA256SUMS` covers the final local source snapshots and every archived remote
attempt artifact. The pinned NUC object store retains the compiled `.olean`
files for the three final green targets.
