# V244 deployed extraction toolchain incompatibility

The unchanged pinned Charon executable cannot use the required deployed Rust
1.94.1 sysroot. This was checked by an actual capped extraction attempt, not
inferred only from its version banner. No alternate extractor or std was used.

Pinned executable:
`/home/dombarker/project-offloads/codex-pv-extract-20261027/charon`
SHA-256 `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`.
`charon toolchain-version` reports `nightly-2026-06-01`;
its compiler is `rustc 1.98.0-nightly (14210df0e 2026-05-31)`.
Required native compiler is `rustc 1.94.1 (e408947bf 2026-03-25)`.

`charon227-deployed-resume4` supplied the explicit 1.94.1 sysroot and
`RUSTUP_TOOLCHAIN=1.94.1`, release/optimized MIR, the owned reference and exact
resolved deployed dependency versions/features. It exited 101 before translating
the owned body. The primary error is:

```text
error[E0514]: found crate `std` compiled by an incompatible version of rustc
crate `std` compiled by rustc 1.94.1 (e408947bf 2026-03-25)
please recompile that crate using this compiler (rustc 1.98.0-nightly (14210df0e 2026-05-31))
```

Full stdout/stderr, command, admission logs and resource receipt are in
`receipts-resume4/charon227-deployed-resume4/`.
The feature graph, both compiler identities, std source path and hashes of
all 1,943 Rust std-source files are in `features227-resume4.json`.
No LLBC or Lean emission was produced. No extraction or source-law credit is
claimed. A switch to the nightly std would violate the explicit D387 deployed
configuration requirement; changing or rebuilding the pinned extractor would
violate the unchanged-extractor requirement and infrastructure boundary.

The task's inherited `local-lean.txt` rule 5 says:
“Do NOT build or repair build/launcher/monitoring infrastructure” and
“Proof work only.” The lead must resolve the pinned-extractor/toolchain
incompatibility before this extraction route can continue. This is an
infrastructure/toolchain handoff with the Lean budget unspent, not budget
exhaustion, a row counterexample, or row closure. V241/V245 have not been started
because the instruction is to finish V244 first.
