# Native packets before extracted-reference closure

K001 failed compilation in our harness: duplicate Vec import from KMX. Removed
our duplicate, retaining the exact KMX source. K002 opening contract PASS; K003
inverted ensures FAIL. Its result predicate is pointer identity to the safe
reference and exact length832, avoiding a whole-buffer comparison. Domain:
proof length57607, i<22. No returned-slice stub is admitted by this result.

K004–K009 establish scalar u64 interface fidelity: body/weak/real PASS;
inverted ensures, unimplied stub caller, modifies violation FAIL.
K010/K011 key contract/caller PASS; K012 wrong caller/K013 inverted FAIL.
K014/K015 same-index contract/caller PASS; K016 wrong/K017 inverted FAIL.
K018/K019 same-leaf contract/caller PASS; K020 wrong/K021 inverted FAIL.
K022/K023 KMX 32-byte copy positive PASS / negative FAIL in exact same config.
K024/K025 row getter contract/caller PASS; K026 wrong/K027 inverted FAIL;
these initial row getter harnesses used a 5-byte backing. Broader backing
checks will be recorded separately; no full token domain is inferred here.

Each run validates frozen resolved dependency edges and lock before execution,
records all-crate features for deployed defaults plus private-leaf-salts,
optimized-terminal,program-build, and checks lock unchanged afterward.
KMX patch sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
Receipts contain command, revision/source hashes, exit, wall, RSS, swap and
axioms (not applicable for Kani). P6/D188 tool trust is reclassified, retained.
No complete four-part frontier closure claimed yet. No shipped files changed;
ELF hashes remain inherited, no rebuild trigger.
