# Lock topology deviation

The final read-only postflight found NCL_src/Cargo.lock was a symlink to the
retained NBY_src/Cargo.lock, rather than a private regular byte copy. This
originated in NCL_native_setup_v1.py's source-tree seed. The code is retained.
The explicit instruction required copying the frozen lock into this lane's
scratch tree, so this is a protocol deviation, not silently accepted compliance.

All50 native runs did validate the resolved dependency versions/edges against
that frozen lock with CARGO_NET_OFFLINE=true, and each checked before/after
SHA2565782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef.
There is no observed dependency/lock-content drift. Exact graph receipts,
metadata stderr, source snapshots, commands and raw outcomes are retained.
The mathematical Lean results are independent of this topology deviation.

Nevertheless, the24 paired local native results are held as protocol-qualified
observations, NOT supplied as unqualified P6 leaf/caller closure credit.
Re-establishment under a regular copied lock, or an explicit lead audit of
per-run equivalent graph evidence, remains a finding for the handoff. This
lane cannot silently allocate another run:50/50 invocations are exhausted.

Correction, after the runs: make the lane's own lock a regular private byte
copy with unchanged frozen hash, preserve the old target untouched, repair
NCL_native_setup.py to copy it on setup, and make NCL_gate.py refuse a symlink.
The corrective receipt is NCL_CLEANUP.json. No native proof is rerun or
retrospectively relabelled by this correction. No shared source, cache,
launcher, reservation script or frozen repository file is changed.
