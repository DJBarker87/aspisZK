# R406 sampler word distribution

The promoted lemma establishes one exact block-sampling fact: under a uniform 32-byte `State`, the eight little-endian 32-bit words split into high 14-bit and low 18-bit coordinates by a finite bijection. Consequently, the eight values after the 18-bit mask are jointly uniform on `(Fin (2^18))^8`.

The proof is a finite-coordinate bijection, not an oracle-independence argument. It does not prove that repeated or adaptive reads from the memoized shared oracle are independent, and it does not establish any challenge, kernel, retry, or security law. The first remaining bridge is to the bounded q22 scan and actual memoized oracle, including cache-hit loss.

The promoted research source is [R406SamplerWordDistribution.lean](lean/AspisV8R19/R406SamplerWordDistribution.lean). Full source snapshots, failed attempts, logs, receipts, axioms, runner, and pinned dependency identities are retained in [the evidence package](evidence/r406-sampler-word-distribution/README.md).
