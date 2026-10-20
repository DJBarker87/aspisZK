# Live external-model check

Copy this directory to the job host workspace as `library-model-check/`,
with the pinned Rust checkout in the sibling `src/`. The Cargo path is for
that host layout; do not run Cargo in the evidence directory.

`library-model-check-v2.py` runs the optimized, capped check. It validates
live Zeroizing<[u8;32]> AsRef/Deref identity, Result::map call behaviour,
P and FIBRE_COUNT. Allocation, drop/zeroization and OS entropy laws are
outside these checks and are not asserted by the Lean adapter packet.
