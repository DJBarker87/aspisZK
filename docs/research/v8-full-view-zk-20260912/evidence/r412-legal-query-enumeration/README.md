# R412 saved evidence

This bundle preserves the successful and two failed focused Lean runs, exact source snapshots, complete logs and receipts, the runner, the promoted source, and local source copies for the immediate imported invariant module and its sampler-program dependency. The immediate imported source `Q22SamplerInvariants` matches the SHA in the green receipt.

The promoted Lean source is byte-identical to the successful run snapshot. Its initial comment calls it an uncompiled draft; this wording is intentionally retained from that snapshot, and the publication note records that the later green run supersedes that historical comment.

`cache-identities.json` records a read-only hash audit of relevant cached `.olean` files after the successful run. The original receipt did not include those hashes, and the file explicitly avoids claiming they were measured at run time. GNU time reports Lean-child RSS; the cgroup wrapper's MemoryPeak is distinct. Failed drafts are retained only as rejected history; they contain `sorryAx` in reports and are not accepted proof results.
