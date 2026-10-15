# Literal read-stability evidence

This focused target proves that appending a suffix after the last inspected row leaves the literal opening view and matching-data reader unchanged. It composes already checked list-index append facts; it makes no acceptance, Rust-source, or security claim.

Attempts `a` through `h` failed during dependent option-match/rewrite proof elaboration and are retained with their exact precompile source snapshots and receipts. Attempt `i` is green: 2.11 s, 3,594,568 KiB peak RSS, zero swap, and two standard axiom reports (`propext`, `Quot.sound`). It ran with a 4G high / 6G max / zero-swap cgroup under Lean 4.32.0. See `source-manifest.json` for all source, object, import, and runner pins.
