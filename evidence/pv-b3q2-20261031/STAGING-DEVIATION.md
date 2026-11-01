# Private Rust mirror staging deviation

The final boundary inspection found that N77115's broad plain copy of the
inherited Rust source mirror also copied 43 unused `.lean` files, including 42
PV_B3P sources, into this job's `direct-source` directory. This breached the
instruction not to create PV_B3P sources, despite the files being unchanged
copies. No new PV_B3P declaration was authored and no original was edited.

The private Rust mirror was absent from LEAN_PATH, and these copied sources
were never compiled or imported. N77121 inventoried every duplicate, verified
it byte-identical to its retained original, and removed only the duplicate Lean
files from that isolated mirror. It then rechecked all originals and every
private PV_B3Q proof source/object unchanged. `rust-mirror-cleanup.json` records
all 43 paths and hashes. Original sources, imported caches and task keys remain
retained. Rust sources and extraction inputs were not changed.

The staging script now excludes `.lean`, `.olean*` and `.ilean*`. No formal
source or dependency changed, so the successful final manifest was not rerun.
This deviation is reported separately from the valid kernel results and from
the still-open complete fmt-1 / source-caller / dependency-closure obligations.
