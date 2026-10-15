# Independent review: selected opening stages

The final source snapshot matches the repository `SelectedOpeningStages.lean` at SHA-256 `c87ad5c67f3c57fbc37dc8394a390a8e45c6a6a638c8cae7d0839af4245c1786`. The three bundled direct-import source files match the repository sources and the source hashes recorded in the manifest: `SelectedPrefixRead.lean` (`6ecff471…eb02dab`), `CircleRecordCodec.lean` (`b1fba8dc…96f71f`), and `OpeningRecordCodec.lean` (`7ac150cf…fd6387`). Their bundled objects match the manifest pins; the final object is present in the archive at the pinned hash.

Attempt a exited 0 in 1.57 s, with 3,587,832 KiB peak RSS and zero swap under 4G/6G/0. The log has exactly four axiom reports, one per append-stability theorem; each reports `[propext, Classical.choice, Quot.sound]`. Bundle `SHA256SUMS` validated before this review was added and is refreshed below.

The theorem statements establish staged read stability at the stated row-prefix lengths (27, 28, 29, and 30). They do not add challenge values, recovered words, or an acceptance result, consistent with the README scope.
