# R424 saved build-evidence audit

Audit result: PASS.

The ordinary clone receipt records 1,084 entries (1,037 regular files and one symlink), equal content/mode manifests before the source overlay, the pinned parent `PrePasses.ml` hash, and zero shared regular-file inodes. This is a saved remote audit result; the remote parent and clone trees were not re-read during this audit.

Both compilation receipts match their saved source snapshots, target names, source revision, GNU-time records, and Docker/cgroup resource records:

- Helper target `.aeneas.objs/byte/aeneas__ConcreteAssociatedTypes.cmo`: exit 0, 3.86 s, 325,292 KiB peak RSS, 0 swaps.
- Integration target `.aeneas.objs/byte/aeneas__InterpUtils.cmo`: exit 0, 12.14 s, 479,240 KiB peak RSS, 0 swaps.

Both used the recorded 5 GiB `MemoryHigh`, 7 GiB `MemoryMax`, `MemorySwapMax=0`, `TasksMax=128` systemd slice. Docker inspection records 5 GiB reservation, 7 GiB memory, `--memory-swap=7g` equal to memory (no extra container swap), 128 pids, network disabled, and the pinned image hash. GNU-time is the compiler measurement; wrapper/service runtime and tiny systemd service memory numbers are not substitutes.

The helper build includes hashes for its `.cmo` and `.cmi`; the integration build has no saved compiled-artifact checksum file. The edited candidate source drafts also match the successful build snapshots. The old `build-preflight/REPORT.md` accurately describes the earlier preflight stage, before clone/build; it is historical and does not contradict the later receipts.

This is typechecking evidence only. No fixtures were executed, and no translation, Lean theorem, source-semantic correspondence, or security result follows. See `audit.json` for per-field checks and hashes.
