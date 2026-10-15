# Literal opening view and event inputs

This bundle contains two focused targets compiled in the pinned NUC workspace at base `3c79ec30fa44f408c716bb345050c137e907fa67`. `R1LiteralOpeningView` reads a typed view from the literal transcript prefix, requiring 25 semantic rows and reading ordinary challenges 25 and 26. `R1LiteralOpeningEvents` builds row-specific event inputs by appending only the current literal message with a dummy challenge.

`LiteralOpeningView-b` succeeded (1.99 s, 3,589,184 KiB peak RSS, zero swap) and emitted two standard axiom reports. Failed attempt `LiteralOpeningView-a` is preserved: it timed out at `read_length`, exited 1, and emitted three reports including `sorryAx`. `LiteralOpeningEvents-a` succeeded (1.56 s, 3,594,256 KiB, zero swap); it contains definitions only and emitted no explicit axiom reports.

This bundle does not establish acceptance, complete event density, efficient extraction, or Rust-source correspondence. All attempts, source snapshots, receipts, logs, time records, direct-import sources/objects, and runner pins are retained.

Object-storage note: the canonical compiled objects are the byte-identical members of `literal-opening-view-events-objects.tar.gz` listed in the manifest. Loose duplicate `.olean` files were moved outside the bundle to `/tmp/aspis-r1-retained-loose-objects-20261015/lean-literal-opening-view-events-20261015/`; archive members and object SHA-256 pins were not changed.
