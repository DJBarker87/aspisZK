# Stage 1: checksum and exact body frontier

Checked: JHh_SHARealization extends the immutable JHe_SHARealization with
three concrete digest equations (proof/public/checksum). Its inherited fields
remain tree0 Fin157, tree1 Fin157, tree2 Fin139. This is 456 equations, no
acceptance or output-identity field. The new extension has a new prefix because
existing proved modules may not be edited.

Each new digest equation is proved unconditionally in its own small module:
JHh_ChecksumEquation.source (007), JHh_PublicEquation.source (008),
JHh_ProofEquation.source (009); only standard axioms.

JHh_ImageIdentity.source (010) checks the exact image/checksum composition.
It deliberately exposes actual-body/retained-body identity, request identity
and retained suffix identity. These are not discharged by SHA. Request/suffix
are being proved separately; the actual-body equation is still OPEN.
The source-selected query accumulator fields were not identified by the
inherited canonicality/length theorems. No saved-byte equality or accepted1
is claimed at this stage. Before/after headline unchanged; zero ledger delta.

Attempts 001-004 rebuild missing unchanged JHe objects privately; 005 ordinary
class-syntax error, fixed by 006; 007-010 exit0. No timeout/memory retry.
Exact target, exit, wall, RSS, swap, source revision/hash and axioms are in
each receipt. No shipped change, Rust, Kani, ELF rebuild, or release replay.
