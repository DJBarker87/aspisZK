# R156/R160 extraction evidence staging (mechanical)

This directory copies the raw artifacts unchanged from `.r21-scratch/r156-full-freeze/` and `.r21-scratch/r160-freeze-std/`. Hashes for each staged payload are in `SHA256SUMS.txt`; hashes cover every staged file except that checksum list itself. Extraction/translation command transcripts are retained verbatim.

Source extraction inputs recorded in `metrics.json`:

- NUC source checkout path: `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`.
- Cargo manifest: `docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml`.
- Callback source: `docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs`, SHA-256 `4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`.
- Staging worktree revision: `ace61fd9721cfb176790943c408d72cab28c9307` on `research/v8-r64-guarded-m31-20260929`.

R156 extraction and translation logs each report exit status 0; extraction wall time 14.63 s / peak RSS 624,952 KiB / swap 0, translation wall time 4.96 s / peak RSS 351,620 KiB / swap 0. R160 extraction reports exit 0, wall 15.35 s / peak RSS 624,572 KiB / swap 0. R160 translation log reports exit 2, wall 4.67 s / peak RSS 346,744 KiB / swap 0; it records `Unexpected access to a global` at `/rustc/library/core/src/slice/iter/macros.rs:28:8–43:27`.

## Syntactic generated-to-promoted diff audit

Compared raw `R156/generated/AspisR156FullFreeze/Types.lean` with production `docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/Types.lean`, and raw `Funs.lean` with production `FunsCore.lean`:

- `Types.lean`: import set changed from `Aeneas` plus generated `TypesExternal` to `Aeneas.Std`, `Aeneas.Data.Discriminant`, `Aeneas.Tactic.RustAttributes`. Generated `@[discriminant isize]` annotations were removed from three enums; three explicit named `Discriminant ... Isize` instances were added (`instR156CircleError`, `instR156CircleSampleError`, `instR156CallbackError`) with constructor-to-integer mappings.
- `FunsCore.lean`: imports changed from `Aeneas` plus generated `FunsExternal` to `Aeneas.Std` and `Aeneas.Tactic.RustAttributes`. Two generated `Std.U64.wrapping_shr` literal arguments changed from `31#i32` to `31#u32` (raw Funs lines 307 and 575). The promoted file ends after generated global `V8_COMPONENT_OOD_VECTOR`; all raw generated definitions following that point are omitted by the file cut (including `bytes`, `sample`, callback closure definitions, `freeze_loop`, and `freeze`). This records syntax only and makes no correspondence claim.
