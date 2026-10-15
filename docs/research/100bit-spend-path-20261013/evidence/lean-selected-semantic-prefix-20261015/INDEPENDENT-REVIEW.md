# Independent evidence review

Reviewed the selected semantic-prefix source and evidence bundle without rebuilding.

- The current source, final-source copy, and green attempt snapshot all have SHA-256 `1c465621c5924f3d0b275ad151b141329a3e541aee4d22c3a831b35451fd22e9` and compare byte-for-byte.
- Both direct-import source copies match the corresponding current worktree files. The three archived object members match the manifest hashes and byte sizes.
- All entries in `SHA256SUMS` verify. The receipt records target `R1SelectedSemanticPrefix`, attempt `a`, exit 0, 2.00 s, 3,588,192 KiB peak RSS, zero swap, and cgroup limits 4G/6G/0 with TasksMax 128.
- The output log contains exactly two axiom reports, for `read_length` and `read_append`; both report `[propext, Classical.choice, Quot.sound]`. No `sorryAx` appears.
- The source parses rows 0–24 sequentially, carries challenges unchanged, and keeps the `recoverC2` callback explicit. `read_append` states the append composition law and `read_length` preserves successful output length. The source and report do not claim trace recovery, acceptance, or Rust/source correspondence.

The output log includes two harmless unused-simp-argument warnings in the failing-option branches of `read_append` (`hl` and `hr`); the target compiled successfully.
