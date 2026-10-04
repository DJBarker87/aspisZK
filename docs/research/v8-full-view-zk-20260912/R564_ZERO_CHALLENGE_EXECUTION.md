# R564: deterministic execution of a zero four-limb challenge

[`R564ZeroChallengeExecutionV2.lean`](lean/AspisV8R19/R564ZeroChallengeExecutionV2.lean)
proves the selected QM31 sampler's deterministic path under the explicit
condition that the first four 31-bit-masked words of the current block are
zero. The four limbs each accept on their first read. The model makes no refill
or rejection call, preserves the initial two squeeze calls and advanced state,
and returns `some [0, 0, 0, 0]`. The final theorem composes that path with the
existing R170 selected-source transcript theorem and its exact
`encodeResult (some [0, 0, 0, 0])` result.

This is conditional deterministic execution evidence. It is not a probability
law for the actual full challenge, a freshness or independence statement for
shared-oracle reads, or a security conclusion. The first remaining proposition
is the actual fresh/shared-oracle law and the admissibility and cost of repeated
attempts.

The exact target `AspisV8R19/R564ZeroChallengeExecutionV2.lean` compiled with
exit status 0, wall time 1.67 seconds, peak Lean-child RSS 3,717,308 KiB, and
swap 0. It used the pinned cached Lean 4.32 workspace, `-j1 -M4500`,
`MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Its
SHA256 is `f3aa191e96613c3b776af257635e9646600a98370217cb504b43d7bc3d4ea509`.
The source revision was `1f8a1b24361584df351751fd4bae11f5690de448`. Direct
local import hashes are recorded verbatim in the successful receipt and
include R551 V10 (`f99ee19cc9d3a471e1e9768a4bee2001a714e6d085f50885929bbaf1ee3ca2b6`),
R170 (`693dc8c748487678b8033cfe85ad8051288b2f759cd3d594f80b15a30e057f6a`),
and R167 (`3d4c55d2b8c9e542d71daa795929c3100cede9784d2c7497cdc2a43734480325`).

The complete `#print axioms` output for all four named theorems is retained in
the evidence bundle. The three execution-model theorems depend only on Lean's
foundational axioms. The composed source theorem additionally inherits
`core.fmt.Formatter`; it is not a standard-axioms-only result. The exact cached
declaration is `@[rust_type "core::fmt::Formatter"] axiom
core.fmt.Formatter : Type` in the pinned Aeneas runtime source
[`CoreFmt.lean`](evidence/r72-sampler/runtime/CoreFmt.lean), lines 12–13,
SHA256 `26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce`.
It is an opaque runtime type used in the generated `Debug` trait signature.
The generated `Result.unwrap` model ignores its `Debug` argument, returning
the value on `.Ok` and `.fail .panic` on `.Err`; this proof does not establish
formatting behavior or remove that dependency. R169/R170 provenance and the
cached runtime pin are documented in
[`R169_CURRENT_INNER_SAMPLER.md`](R169_CURRENT_INNER_SAMPLER.md) and
[`evidence/r169-current-inner-sampler/manifest.json`](evidence/r169-current-inner-sampler/manifest.json).

The evidence directory preserves the original failed draft, every focused
attempt, the successful deterministic-model predecessor, the failed first
composition attempt, and the final source/log/receipt with recursive
checksums. No Lean rerun or commit was made during evidence packaging.
