# S10 adopted-source re-pin — 22 October 2026

## Stage 1: artifact reproduction

Source revision `7acf5cfb5fa49f4cf5d8e69566ba8221189c31ac` in this worktree.
`source-inputs.json` pins the 488-file historical census and the additional
current Rust/workspace inputs needed for Cargo path dependencies. The private
host snapshot was rehashed in full. No source or candidate was changed.

All three optimized builds reproduce the approved release pins:

| Build | SHA-256 | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|
| default | `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0` | 41.805 | 684024 | 0 |
| devnet | `12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f` | 36.968 | 684568 | 0 |
| pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 31.565 | 677480 | 0 |

Each build ran in its own 6G/8G/zero-swap/64-task scope, with `-j 4`,
platform-tools v1.52 and the retained release features. Expected time was in
optimized compilation and diagnostic emission, not arithmetic elimination.
Commands, resource reservations, complete compiler warnings, exits and
host-only artifact/MIR/LLVM/mono SHA/size pins are in `build-manifest.json`
and the build directories. No binary, object, tarball or key is committed.
The Cargo-generated task keys remain on the private host; no cleanup occurs.

The first preflight failed before compilation because the old source census
omitted research path-dependency manifests. Its receipt is preserved; the
replacement adds those current inputs. The reused receipt harness hard-codes
historical revision b2727acd; **that receipt field is not the actual source**.
The explicit correction in build-manifest and source-inputs identifies the
actual revision and exact input hashes without rewriting raw receipts.
Compiler stack-frame diagnostics remain visible; artifact identity alone is
not runtime safety or source refinement. `#print axioms`: N/A, no Lean run.

S10 completeness and the S2 caller identities remain open. Historical pass
1–5 certificates are untouched. Target not yet established.
