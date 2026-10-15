# Semantic coefficient codec focused evidence

This bundle preserves the focused Lean target for the strict 32-byte low-Wide codec and fixed 28-coefficient payload codec. It does not prove record framing, row-to-codec instantiation, or Rust caller correspondence.

Source base at task start: `6459d24bcd83bf12441b606d8031b6c9301bc320`. Target: `R1SemanticCoefficientCodec`.

Four attempts are retained with exact source snapshots, receipts, logs, time logs and hash sidecars: attempts a–c failed during proof plumbing; attempt d is green. The final source snapshot matches receipt d. The object archive contains exactly the final target object. The runner and Lean environment pins are retained in `runner/`; direct imported source/object pins are listed in `source-manifest.json`.

The green output contains ten `#print axioms` reports, each using only `[propext, Classical.choice, Quot.sound]`. Receipt d records exit 0, 2.82 seconds, peak RSS 3,325,448 KiB, zero swap, and 4/6 GiB memory caps with 128 task cap.
