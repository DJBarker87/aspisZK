# Independent evidence review

Reviewed against the saved source snapshots, current repository files, attempt receipt, raw logs, object archive, and checksum index. The target and both direct-import source hashes match the current repository bytes and their bundle snapshots. The single attempt `literal-transcript-a` has matching receipt, sidecar, and source hash; it exited 0 in 1.95 s with 3,581,068 KiB peak RSS and zero swap under the recorded 4G/6G/0 cgroup. Its five `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The three expected archive members and their hashes/sizes match the manifest.

The checked statements are `erasePrefix_round`, `erasePrefix_ext`, and append-stability of the word lookups `c1At`, `c2At`, and `vAt`. These are carrier/projection/list facts. They do not establish byte-decoding correspondence, accepted-proof recovery, classifier density, Merkle compilation, source refinement, or security closure.
