# Independent evidence review

Reviewed 2026-10-15 by a second agent, without rebuilding Lean.

The manifest's final source hash matches the packaged source, captured attempt snapshot, receipt, and current repository `lean/RawRoundCanonical.lean` at SHA-256 `6eba5fad8a8916e9f2418a863a04e192bff1cc4ed3267cfc4b507b581cd107d8`. Its direct-import `R1RawRoundDecode` source/object pins match the preserved copies. The archived target object hash/size and all `SHA256SUMS` entries validate. The attempt exited 0 in 0.78 s with 1,806,296 KiB peak RSS and zero swap; its single public axiom report lists `propext`.

The theorem `RawRoundCanonical.encode_of_decode` is conditional on `hcanonical`: every successful message decode re-encodes to the same bytes. Under that premise, successful list decoding re-encodes the entire raw record list. This review records artifact and theorem-shape checks only; it makes no source-correspondence claim.
