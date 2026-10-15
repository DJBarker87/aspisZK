# OpeningRecordCodec independent review

The final source, current worktree source, and green attempt-b snapshot all match SHA-256 `7ac150cff7ede99cf4916e81e8ba348bdcf785e6d7771cf46aa9622756fd6387`. The bundle checksum list verifies. All direct-import source pins and every archived object member’s size and hash match the manifest; the current manifest SHA-256 is `232d87f5cfca8c0fc30ea9c64f3edf1c07f3deaad44f72a8a4e60714850dc07f`. Attempt b exited 0 in 2.18 seconds at 3,580,928 KiB peak RSS, with zero swap under the recorded 4G/6G/0/128 cgroup. Its eight axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.

Attempt a is preserved as a failed predecessor: it exited 1 and all eight of its diagnostic axiom reports contained `sorryAx`; those are not successful audit reports.

The six typed payload layouts and lengths agree with the selected-row contract: 29 low-field values (928 bytes), one wide value (32), seven wide values (224), a 32-byte state plus seven wide values (256), 64 wide values (2048), and an empty payload (0). Each record adds the four-byte tagless length frame, producing record lengths 932, 36, 228, 260, 2052, and 4. The row/domain label is external to this payload codec. The source proves model encoding/decoding inverses and bounded message uniqueness; it does not establish Rust parser refinement, causal recovery, acceptance, or a probability theorem.

See [review.json](review.json) for the checked pins and receipts. The original package remains at [lean-opening-record-codec-20261015](../lean-opening-record-codec-20261015).
