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

## Stage 2: regenerated ELF, compiler and CFG observations

`analysis-manifest.json` pins every output. The old pass 1–5 generators are
adapted only for private input/output paths, adopted hashes and build labels;
`generator-adapters.json` pins the original and adapted scripts. The ELF-only
collector does not rerun the historical LLBC extraction. Full compiler and
inline observations remain observations, not an extraction-success claim.

LLVM objdump independently agrees with all 1,603 call instructions per
verifier (previously 1,593) and all 2,202 Pool calls. Callx counts remain
36/36/80 and relocated code-pointer candidates 17/17/26. Raw symbol aliases,
new ELF IDs, exact address/size data, direct-call reachability lower bounds,
relocations and missing DWARF are recorded. The 1,042 nonzero emitted symbol
records have no unassigned or multiply assigned ownership proposals; the
lead re-pin's source overlay is embedded without recycling historical IDs.
No complete reachable/inlined declaration set is asserted.

The retained frozen compiler inspectors regenerate all forty frontier
observations for each mode, LLVM symbol-definition matches, and 120 typed
instance observations. The 5,579,614-byte `instances.json` stays on the host,
with SHA and generator retained; thirteen records are BODY_ONLY. The stripped
release ELFs still have no transferable DWARF inline map. Prior debug-build
failures remain historical, not a map for the adopted binaries. No new debug
candidate or Lean build was necessary.

All 140 selected-call dominance relations are re-established on newly
extracted graphs (`cfg.json`, `ordering-repin-map.json`). Ten of the twelve
nonempty function graphs are byte-identical at the edge-list level. Each
TX2_common graph changes because of the adopted inlined powers<29> loop:
38 facts have changed body hashes; 28 change before/after block coordinates.
The selected call identities, argument constants and all 140 relations survive.
Every new graph cut is independently checked in Python. The generic Lean
strict-path mathematics is retained, but the old TX2 graph specializations
remain historical; no new Lean specialization is claimed. This does not prove
source_order, model_order, or a concrete source Calls tree.

The same callback-flow resolver and independent replay recover 15 SHA callback
targets and six null observers, with 131 open library dispatch sites. All 189
negative controls reject. These are compiler-flow observations under the
retained compiler/ABI boundary; library specifications and source refinements
remain obligations. `callback-validation.json` records the focused replay.

`inventory.py --check --require-complete` must still exit 2, including pending
S2 caller identities. No headline premise is removed. All host analysis jobs
have exact command/script/revision, exit/wall/RSS/swap and reservation receipts
under this directory. Raw harness receipts retain the historical hard-coded
revision field; analysis-manifest explicitly corrects it to the source-input
pin. `#print axioms`: N/A for new work; no theorem was added or compiled.
