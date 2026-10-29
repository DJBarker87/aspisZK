# Source roles, not effect laws

All 62 previously empty `effect_class` fields are filled in the new
`effect-interface.json`, preserving every original function ID, LLBC signature,
and static call/drop site. Each changed row includes the pinned definition,
its source-file SHA-256 and caller excerpts. `source-definitions-62.json`
records the independently read dependency/application definitions;
`definition-frozen-source-check.json` verifies the 18 application source files
against baseline git blobs. The six opaque constant initializers have no
static function-call sites; this is recorded rather than fabricated.

The classification distinguishes message construction from RPC sending,
address derivation from account creation, configuration heap-size metadata
from host allocation, and Duration conversion from an actual clock read.
`anyhow::format_err` retains its backtrace/environment subeffects explicitly.
Hash/PDA/trace/encoding operations retain allocation/panic/callee obligations
conservatively. No class labelled `pure-library` asserts an effect-freedom law.

The other 374 operation classifications remain inherited, unverified candidates.
In particular, the old matcher's clock rule scans the whole serialized Rust
name, including generic types; finding `Instant` there can incorrectly label
an unrelated generic operation `clock`. The new artifact adds `rust_ident_path`
and a per-row `classification_status`, so this inherited data cannot be mistaken
for the 62 source-audited rows. It does not silently promote the old candidates
into a complete runtime effect law. A full transitive effect/allocator/drop/
abort adequacy proof remains an existing obligation. No ledger row is removed.
