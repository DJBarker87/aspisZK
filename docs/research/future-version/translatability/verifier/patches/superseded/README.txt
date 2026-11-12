tp1-p0-restore-pinned-text.v1.patch (sha256 22adb5a3246292b805caa07a70c8503a8a9c915b36c3aa6e7c2cdf1da632f7eb)
First version of the restoration patch. Superseded; kept as the record of a failed gate. It switched `semantic_value`
on `feature = "future-lazy-horner"`, a feature the verifier crate did not have, so the deployed build compiled the
pinned `semantic_value` and the recorded payments cost 9,276 (transfer) and 9,238 (withdrawal) units more than the
base. Gate name tp1-p0 on the host; stopped by hand at the worst-case tool build; no GATE_tp1-p0.done exists.

tp1-p0-restore-pinned-text.v2.patch (sha256 afce19eda5b4e80564ba3cd52ebd94da178f6d0fc127dd8408b74bc3a87c67ff)
Second version. Superseded. It restored the pinned `prepared_claim` as well; every gate passed (gate tp1-p0b) except
the compute condition: 1,845 units more than the base on every measured case, all of it from `prepared_claim`
(inlined into `Prepared::new`). The third version leaves `prepared_claim` to patch 1.
