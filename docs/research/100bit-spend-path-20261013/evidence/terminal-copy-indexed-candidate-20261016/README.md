# Isolated terminal Copy-helper and indexed-fold candidate

The compact archive records the three capped extraction stages, exact input
snapshot, original and metadata-only adapted LLBC, generated Lean, source
patches, and old/new generated block comparison. The candidate is not adopted
production source and has no new CU or full Lean verification claim here.

`root-review.json` independently checks 133 source rows, three changed input
files (including the merged crate root), raw timing and resource receipts,
embedded LLBC source contents, the single constructor metadata rename, four
transparent terminal entrypoints, and the old/new generated docblocks.

Unpack the archive and run:

```sh
python3 audit-candidate.py PATH/attempt-fromfn-copy-indexed
```

This is an evidence audit and performs no build or proof replay. The archive's
`SHA256SUMS` records all retained files. Its three stages exited zero under
4 GiB high / 6 GiB max / swap-zero scopes. Rust used release opt-level 3.

The old `candidate.patch` targets preliminary source-kit framing; the new
`actual-merged-input.patch` exactly reconstructs the retained merged input
from its three archived F base files. Raw stage receipts and runner are
unchanged. The old output inventory labels an opaque string as `O`; the
independent root review records its full `Opaque` tag.

The external templates fall from 20 to 17: array from_fn and the two owning
iterator step templates disappear. Seventeen remain unresolved by this
extraction experiment. The adjacent map distinguishes direct calls from
unresolved indirect trait dispatch, and records limits on historical reuse.

Later focused source-slice proofs must be cited separately. They do not turn
this extraction run into a complete terminal or accepted-verifier theorem.
