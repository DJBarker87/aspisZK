# Raw round canonical-decoding lemma

This focused Lean result proves that a successful raw-record decode is reversible when every successful payload decode re-encodes to the original bytes. The canonicality premise is explicit; `decEnc` alone is not used as a substitute. It does not establish source correspondence or protocol acceptance.

Target `R1RawRoundCanonical`, attempt `a`: exit 0, 0.78 s, peak RSS 1,806,296 KiB, zero swap, under 4G/6G/0 and TasksMax 128. The single public theorem audit reports `[propext]`. The source revision, direct import pin, source snapshot, runner files, receipt/logs, and object archive are recorded in `source-manifest.json`.

Final source SHA-256: `6eba5fad8a8916e9f2418a863a04e192bff1cc4ed3267cfc4b507b581cd107d8`.
