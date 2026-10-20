SUPERSEDED: v12 imported generated Funs, which transitively imported the Aeneas function-external template. Do not treat this as accepted evidence. Corrected source and receipt are in ../unrolled-driver-firststop-v14/.

# Query31 unrolled driver first-stop proof (v12)

This is a source/evidence packet for the unrolled decoder candidate. It does not
modify production and does not prove equivalence to the original iterator-based
Rust driver.

`Query31UnrolledDriverFirstStop.lean` imports the checked, option-sanitized
Aeneas owner `AspisR1Query31Transcript.Funs` (object SHA is recorded in
`firststop-evidence/receipt.json`). The imported source and its normalization
record are under `generated/`, `owner-stages/`, and
`source-normalization-manifest.json`. Normalization removes generated
`maxHeartbeats`/`maxRecDepth` commands and their comments; it does not change
definition bodies. The original generated output hash is recorded in the input
manifest. `check_driver_copy.py` compares the normalized generated
`queries_from_pairs` body against `queries_from_pairs_with_scan` after exactly
two substitutions: the initial `Default.default` state is supplied as `scan0`,
and each generated `QueryScan.scan` call is supplied through `scanFn`. It checks
both files against their pinned hashes.

The generated `finish` and `finishAdvance` behavior remains concrete and is
proved by `finishAdvance_success` and `finish_success_iff`. The success-inversion
theorem `successful_driver_has_trace` proves that any successful call to this
adapted eight-branch driver has one of the actual first-stop traces. Indices
0–6 carry the preceding false scan results and a true scan at the selected
index; the final branch carries false results for 0–6 and permits either boolean
at index 7, matching the source's ignored final boolean. Each branch retains
the concrete finish success and the selected `advances[index]` lookup. The
theorem does not assume scan outcomes or finish success independently.

The only explicit runtime boundary in the adapted driver theorem is `scanFn`
(and the initial state `scan0`). This packet does not establish that this
boundary is the same nominal `QueryScan` implementation as the earlier
`QueryScanActualScanBridge`/`QueryScanFiniteCorrespondence` owners. Their state
records have matching fields (`accepted`, `accepted_len`, `draws`) but reside in
different generated namespaces, so an explicit record conversion and scanner
operation correspondence are still needed. The generated FunsExternal template
also declares Aeneas runtime operations; the theorem axiom audit is for the
three exported theorems, each of which reports only
`[propext, Classical.choice, Quot.sound]`. No Aeneas external axiom is used by
those theorem proofs. A separate adapter remains necessary to instantiate the
scan boundary from the earlier scanner proofs.

This is candidate evidence, not a production acceptance or release claim. The
unrolled Rust source remains a refactor candidate, and equivalence against the
original iterator implementation is open.

## Focused Lean receipt

The exact target was `Query31UnrolledDriverFirstStop`, source SHA
`00847b99888fbca344fe009894ac56cf29cee524c2d2b23e336e19dbcab9d89f`, Lean
4.32.0 SHA `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The NUC attempt in `firststop-evidence/receipt.json` exited 0 in 1.806 s,
with peak process RSS 2,584,624 KiB, cgroup peak 318,029,824 bytes, and zero
swap. The scope had MemoryHigh 1 GiB, MemoryMax 2 GiB, and MemorySwapMax 0.
The log prints these axioms for `finishAdvance_success`, `finish_success_iff`,
and `successful_driver_has_trace`:

```
[propext, Classical.choice, Quot.sound]
```

One no-op `change` tactic linter warning remains in the successful source; it
does not affect the result. v12 supersedes earlier first-stop attempts in this
candidate packet. Generated-owner extraction receipts and normalized sources
are included so the direct import and owner lineage can be reviewed. No `.olean`
artifact is included.
