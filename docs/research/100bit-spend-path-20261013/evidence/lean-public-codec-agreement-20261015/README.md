# Public codec agreement

`R1PublicCodecAgreement` proves two Lean-level byte representation equalities: the composed u64 codec emits the same eight bytes as the list-level public index codec, and the composed public codec encoder agrees with `SemanticPublicWire.encode` for both transfer and withdrawal variants. The target compiled at base `3c79ec30fa44f408c716bb345050c137e907fa67`; attempt c succeeded in 3.54 s (3,331,532 KiB peak RSS, zero swap) and emitted two standard axiom reports. Attempts a and b are retained as failures; each emitted two reports containing `sorryAx`.

This is an equality between two Lean wire models. It is not a proof that the Rust parser or serializer implements either model, nor a J1 source-correspondence or security result.

Provenance caveat: `R1PublicByteCodec.olean` was missing from the pinned NUC object directory before compilation. The exact object was restored from the earlier green `lean-public-byte-codec-20261015` evidence archive and matched its recorded object hash (`409de20b1c8aa4b221fc2e24013630a0cd31c7e0917ca31a313f81c011bbf6d1`). The prior bundle records its source SHA and green attempt. This checkpoint retains the import source and object and does not claim a fresh compilation of that dependency.

All three attempts, receipts, source snapshots/sidecars, logs, time records, direct-import sources/objects and pinned runner files are retained.

Object-storage note: the canonical compiled objects are the byte-identical members of `public-codec-agreement-objects.tar.gz` listed in the manifest. Loose duplicate `.olean` files were moved outside the bundle to `/tmp/aspis-r1-retained-loose-objects-20261015/lean-public-codec-agreement-20261015/`; archive members and object SHA-256 pins were not changed.
