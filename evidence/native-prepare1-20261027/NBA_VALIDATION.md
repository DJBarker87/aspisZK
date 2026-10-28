# Final static validation notes

NBA_verify.py launches no builds. It checks exact caps, admission exit0 plus
allowed=true, source snapshots, fresh per-run frozen graph/lock gates, offline
optimized Kani, accepted standard axioms, all78 current theorem roots, source
hash coverage and scope/budgets. Zero structural errors. Its initial assumption
that every historical run had the later source-scan format was repaired to
inspect each retained format and expose the missing historical scans explicitly.
No fresh scan was fabricated and no graph/lock requirement relaxed. The rejected
K002 compile lacks a full patch/manifest and receives no proof credit.

NBA_inventory.py now requires explicit END and cannot overwrite the initial
inventories. NBA_library.py matches219 main plus3 sidecar hashes against the
inherited coherent manifest and final capture. NBA_association.py validates
eight exact lexical transformations; lexical identity alone has no whole-source
proof credit. NBA_finish_host.py hashes tool binaries at end and deletes only
the own target/tmp allowlist, retaining the persistent leaf cache and source.

Both own runner scripts now refuse when NBA_BUDGET_STOP.json exists. This is
stricter budget enforcement, not a change to shared build infrastructure.
No Rust/Lean/Kani job was launched after the30th Kani run. No unchanged full
regression, frozen release manifest or three-ELF rebuild was run: no shipped
source changed, and the native composite remains OPEN.
