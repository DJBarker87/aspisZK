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

## Stage 3: declaration, instance and edge deltas

`mir-diff.json` lists every changed frozen MIR signature/body with raw and
coordinate-normalized hashes, both inline-scope sets and call-edge deltas.
Each verifier has one added helper, four removed closures and twelve changed
bodies (17 records); 4,634 current emitted functions replace 4,637 historical
ones. Pool has 4,921 unchanged functions. `change-assessment.json` explains
each record and records its proposed owner. The direct changes are the S4 dot
entry/helper, S5 canonical constructor, and S3 powers loop; unchanged callers
change through the old/new inline scopes of these bodies. This includes
S8 `EbyKDot::push`, `checked_q`, `prepared_claim`, Prepared::new, TX2_common
and four Weights methods. No other substantive MIR body delta was observed.

`mono-exact-diff.json` retains all 91 changed exact compiler mono-record
spellings per verifier. `mono-diff.json` groups them into 35 buckets after
source-coordinate normalization; the exact list prevents distinct closure
spans from disappearing into that grouping. `llvm-diff.json` lists every
changed emitted declaration/definition multiset (160 per verifier), full-text
hashes and direct-call deltas. Metadata and layout-only text changes are
included, not called source semantic changes.

`elf-diff.json` retains every old/new symbol record within all 306 changed
symbol-name groups per verifier, including duplicate names, sizes, addresses
and raw instruction-body hashes. The 31 changed endpoint-name edge multisets
are individually listed, with full old and new instruction-address call tables
in the retained ELF graphs. No same-name instances are guessed equal. Four
symbol names are added (the dot helper and three powers specializations), and
three old array::try_from_fn symbol names disappear. Pool's symbol, body,
instance and edge comparisons have no delta. All new/removed edge callers are
the adopted routines, their reached callers, or the removed array lowering.

The final comparison is v3. v1 lacked the exact mono/LLVM text lists; v2 added
them; v3 corrected symbol-name grouping to retain duplicate records rather
than selecting one. Their exact script snapshots and receipts remain retained.
Only the final diff-manifest hashes identify the final exhaustive output.
This is a Python evidence correction, not an unchanged build rerun.

`declaration-ownership.json` pins the 14,189 newly emitted generic-body records
(4,634/4,634/4,921) with one proposed semantic owner per occurrence. The full
8.2 MiB JSONL and 31,994,054-byte MIR calls/inline-scope census remain on the
host with exact SHA/size pins. `ownership-reconciliation.json` includes the
lead's 161-entry overlay (160 historical candidates plus the new helper),
explicit historical closure dispositions, and current census summary. Caller
glue placement remains a lowering obligation, never a new trust admission.
These generic supersets are not complete deployed reachable declaration sets.

The whole 488-file source diff is **not confined to three files**: sixteen
files differ, including thirteen pre-existing prover/simulator/wire/statement/
checkpoint-test differences. All are listed with old/new hashes in
`change-assessment.json`. The narrower observed frozen MIR body/call delta is
confined to the three adopted files and their inlined callers; no unexplained
selected-compiler body change or Pool artifact change was found. This does not
assert global semantic equivalence or a full extraction of the current tree.
`gates.json` remains INCOMPLETE/exit 2, with S2 caller identities explicitly open.
