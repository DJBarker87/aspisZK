# Current selected-mask extraction

The unchanged production selected-mask function and its reachable helpers have
been extracted through Charon/Aeneas. Both generated Lean files compile against
the actual cached Aeneas runtime. The output includes the prepared multiplier,
coefficient-fill loops, reverse Horner loop, selected-linear loop, tower-basis
transforms and explicit fixed-power chain. This is a concrete proof input, not
yet a theorem that the mask evaluator equals the security model.

`extraction.tar.gz` preserves both attempts and the full standalone input,
source/tool pins, build script, LLBC, generated Lean and stage receipts. The
first attempt failed before LLBC because the standalone scaffold omitted
production `build.rs`. The second adds that unchanged file and compiles the
lookup-table generator with optimization level 3. All production sources remain
unchanged. No target or dependency cache is archived.

The extraction input is pinned at `70f8edc9d`; subsequent proof/document commits
did not change those production files. Charon took 47.31 monotonic seconds with
817,392 KiB sampled aggregate RSS; Aeneas took 1.511 seconds with 115,888 KiB.
The two Lean checks at `4393b4992` used 16.022 and 8.551 monotonic seconds,
respectively, and peaked at 2,772,704 KiB sampled aggregate RSS. Every retained
process swap count is zero. Exact targets, commands, source/object hashes and
raw timing metrics are in `lead-review.json` and the logs.

There are no axiom reports in these two generated definition files; their
successful compilation must not be counted as a correctness theorem. The
frozen extraction plan predates these checks; this README and root review
record the later compilation result without altering the extraction archive.

The [reuse plan](proof-reuse-plan.md) identifies twelve common field functions
and the global P that match the previously checked arithmetic extraction after
namespace normalization. The next step is to retarget those existing proofs,
then prove the prepared multiplier and actual mask loops. Their different Lean
namespaces require checked adapters or retargeted proofs, not an alias-only
claim. Acceptance, terminal correspondence and the full private-spend security
theorem remain open.
