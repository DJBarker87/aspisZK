# Literal run evidence

This bundle records the focused `R1LiteralRun` proof. It relates the recursive literal-message transcript to its erased byte-message projection, proves the round count, and reuses indexed-read append stability. It does not provide decoding, accepted-proof recovery, source correspondence, or a security result.

Both attempts are retained. Attempt `a` failed; attempt `b` passed with three standard axiom reports (`propext`, `Classical.choice`, `Quot.sound`) in 1.60 s at 3,578,556 KiB peak RSS and zero swap under the 4G/6G/0 cgroup. See `source-manifest.json` for full source, import, object, runner, and receipt pins.
