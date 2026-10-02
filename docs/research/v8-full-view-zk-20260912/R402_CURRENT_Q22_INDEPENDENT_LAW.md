# R402 bounded q22 result-kernel law

`AspisV8R19/R402Q22IndependentLaw.lean` compiled successfully. For every fuel and scan state, every rational test of the complete result—error or accepted index list—has the same mean under independent oracle answers for every incoming transcript state. The selected count=22, bound=2^18, max_draws=64 program is a specialization. The proof retains its stopping and error branches; it does not assert a law for the returned transcript state or oracle-call trace.

Run `1790960164935938000`: exit 0, 1.33 seconds, GNU-time Lean-child peak RSS 3,227,020 KiB, zero swaps. Source revision `13617a70553ed3c43cee312acba2407b29a7052d`, SHA-256 `69ec6b7ec3b2429b77ca227dc1738c973080bd9d58a1958abf452d109381a1ff`. Pinned Lean 4.32 cache, `lake env lean -j1 -M4500`, systemd 5 GiB high / 7 GiB max / zero swap / 128 tasks. All three complete axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The promoted source is byte-identical to its successful compile input. No failed attempt or unchanged replay was needed.

The memo-table corollary leaves `FreshFrom` explicit. That is not a supplied source assumption: the unguarded multi-block sampler can revisit addresses if an advance answer repeats a prior state. Applying the result to the shared oracle therefore requires the existing guarded-first-read construction plus a quantified cache-hit loss. No shared-oracle freshness gate is closed here.

The first remaining proposition is to bind the actual memoized q22 source experiment to this kernel with that loss, and prove the uniform candidate-word/query-tuple law before conditioning on acceptance or publication. Full callback chronology, universal joint C1/H1/G compatibility, seed/commitment behavior, full-view simulation, retries and soundness remain open. Verifier source, authentication, rejection behavior and all security parameters are unchanged; the 999,790 / 999,532 CU results are preserved without rerunning benchmarks.

Exact source, dependencies/cache audit, runner, raw log, receipt, complete axiom output and a portable checker are in [the evidence bundle](evidence/r402-q22-independent-law/README.md).
