# R489 word arithmetic

## Verified run

- Target: `AspisV8R19/R489WordArithmetic.lean`
- Source revision: `a9c2ad3d78c693f597c050674eb19592bf76f990`
- Canonical source SHA-256: `ac6766da5acfc45ac29bfe3c00d927a495b2104c08b87f745356de1f77da04d5`
- Green run: `1791041878668644000`; exit 0; wall 1.10 s; peak RSS 2,529,752 KiB; swap 0.
- Scope: `systemd-run --user --wait --collect --pipe` with MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128; Lean flags `-j1 -M4500`.
- Direct local import: `AspisV8R19.R195CountedSliceFoldArithmetic` SHA-256 `a6d981971af09a884c447bec037fcb17429d5dadb7a37fa4035e78b29f5bf205`.
- Runner SHA-256: `d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea`.

The promoted canonical source is byte-identical to the successful source snapshot and the original unverified draft: SHA-256 `ac6766da5acfc45ac29bfe3c00d927a495b2104c08b87f745356de1f77da04d5`.

## Proved boundary

For arbitrary `Usize`, R489 proves successful `UScalar.div` and `UScalar.rem` by four with their natural-number values, wrapping multiplication by one, the constant divisions 4/1 and 1/1, nonzero/zero divisor guards for one and four, and the div/rem-by-four partition.

The complete seven `#print axioms` reports from the green run are preserved in its receipt and log. None contains `sorryAx`.

This does not prove an actual parser, source execution, alignment, memory execution, or the selected length 699. The first remaining proposition is an actual generated-source bridge using compiler-evaluated globals 4 and 1.

## Preserved rejected attempts

- `1791041682327544000`: exit 1; 1.02 s; 2,520,856 KiB; swap 0. Its partial proof had type/identifier and arithmetic-order errors; four axiom reports still contained `sorryAx`.
- `1791041772444447000`: exit 1; 1.05 s; 2,518,960 KiB; swap 0. It used incorrect result-level expressions and an unavailable helper; five reports contained `sorryAx`.

Exact source snapshots and receipts are retained beside this note. Complete readable logs are retained as `.log`; the matching `.log.base64` files preserve each original raw log byte stream, including its initial CRLF line. `SHA256SUMS.txt` records every raw checksum.
