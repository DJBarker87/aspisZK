# Selected typed-read composition evidence

This target defines semantic, opening, and full-transcript payload readers over typed duplex-record lists by applying the selected raw-record encoder. Under successful raw decoding, each typed reader equals its existing raw reader. It also proves append stability using the existing row bounds 24, 31, and 32 plus encoder append/length facts. These are representation and list-model results; they do not establish source-parser correspondence, accepted transcript behavior, or Rust refinement.

Attempt `R1SelectedTypedReads-a` exited 0 in 1.48 s, with 3,581,000 KiB peak RSS and zero swap under 4G/6G/0. All six public axiom reports list `[propext, Classical.choice, Quot.sound]`. The deterministic object archive includes the target and all five direct imports. Exact source, imported source, object, runner, and attempt pins are recorded in `source-manifest.json`.
