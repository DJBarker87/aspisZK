# R690 circle-generator certificate

R690 proves a mathematical certificate for the selected literal CM31 generator `g = (2, 1268011823)`. It records 31 named successive-square values in `CM31Exact`, proves the generic identity `square^[k] g = g^(2^k)`, and derives `g^(2^30) = -1`, `g^(2^31) = 1`, and `norm(g) = 1`.

Each concrete transition is a separate explicit integer modular-arithmetic certificate in `ZMod (2^31 - 1)`. The proof never unfolds or kernel-reduces `g^(2^31)`, and uses neither `native_decide` nor a custom arithmetic axiom.

Final focused target: `AspisV8R19/R690CircleGeneratorCertificate.lean`; run `1791123411214835000`; exit 0; wall 2.18 s; peak Lean-child RSS 3,280,436 KiB; swap 0. Source revision `8a2de33e903d47b18b81cbaf335a0a7a5c1896ff`; source SHA-256 `8f098967edceb48854014a5a0fb5711ee105644c5440e2ff35614219779406a2`. It used the pinned Lean 4.32 cache with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The complete axiom reports for `square_iterate_pow`, both power identities, and `g_norm_one` are each `[propext, Classical.choice, Quot.sound]`.

The frozen source pins for the literal and circle profile are preserved in [SOURCE_PINS.md](evidence/r690-circle-generator-certificate/SOURCE_PINS.md). This result does not prove the selected fast table, bit-reversal, or domain-root implementation corresponds to these powers; that is the first remaining bridge. It makes no native-execution, callback, privacy, or security claim.

All changed failed and intermediate focused attempts are retained in [ATTEMPTS.md](evidence/r690-circle-generator-certificate/ATTEMPTS.md).
