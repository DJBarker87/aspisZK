# R569 Aeneas Option-language-item and prior capture inventory

Read-only comparison for the Aeneas failure on `R569MaskedClaimWithFrom.llbc`; no recapture or tool/source change was made.

## Current R569 output

`R569MaskedClaimWithFrom.llbc` is SHA-256 `e1670d259f43aa411c49fd7e763814a4d790358b0e8f008184424c032f2bbc81`. Its Charon options record `monomorphize: true`, start root `crate::claim_probe`, and includes `core::option`, `core::result::_::map_err`, `aspis_core::state_only_hiding::begin_state_only_masked_sumcheck`, `aspis_core::state_only_hiding::_::from`, `aspis_core::transcript`, and `aspis_core::field`.

It contains **two** `type_decls` entries with `item_meta.lang_item = "Option"`: type IDs 13 and 20. Both are instantiated names `core::option::Option<...>` with distinct payload types (`Deduplicated: 1509` and `Deduplicated: 2161`). This matches Aeneas's exact error: “Nested-loop returns require exactly one Option language item” at `transcript.rs:421:4–421:86` (`PrePasses.ml:918`). This is a type-declaration count in the captured JSON, not a claim about Rust source defining two Option enums.

## Existing successful captures

- R72 LLBC SHA-256 `3c4230aa89a7e711361ba72dc67b3d7106bbfe28eb34fa5ca334d4e14c24991e`; extraction command is recorded in `evidence/r72-sampler/selected/commands.json` and runner in `evidence/r72-sampler/selected/extractor.py` (SHA-256 `fbea904747f208dae1274f6e5bd74ff51b8527aac8b2b4f8fa8d9484094e50a9`). It starts at `crate::sampler_probe`, includes `core::option` and `core::result::_::map_err`, uses `--mir built --sysroot default`, and **does not pass `--monomorphize`**. LLBC records `monomorphize: false` and exactly one generic Option language-item declaration. Translation with the requested pinned Aeneas binary succeeded. Captured `Transcript` includes a higher-ranked `FnPtr` hash field; this route therefore demonstrates successful handling of the `HashFn` field in a non-monomorphized transcript capture.
- R156 LLBC SHA-256 `d9c767a390ac30833c1b63cd6cd882b2124cc510132ce11e6b0eecf3bede2b13`; command is `evidence/r161-current-base-arithmetic/R156/extract-command.json`, translation args are `.../R156/translate-command.json`. It starts at `crate::freeze`, includes `core::option`, `core::result::_::map_err`, `aspis_core::field`, `aspis_core::circle`, and `aspis_core::transcript`, also without `--monomorphize`. LLBC records `monomorphize: false` and one Option language-item declaration. `Transcript` again carries the higher-ranked hash function pointer field.
- R173 is not a new Charon/Aeneas capture. Its artifact is a Lean execution proof over previously established source/model modules; see `evidence/r173-current-nonzero-sampler/manifest.json`. It provides no separate LLBC mode or flags to compare.

## Candidate route for lead decision (not run)

The established mode most directly matching this error is to recapture the same staged wrapper/source with the identical R569 roots/includes and flags, **omitting only Charon's `--monomorphize`**. The prior R72/R156 runs establish the invocation pattern and generic Option shape, but do not prove this exact R569 wrapper capture will succeed. A new capture would need a fresh filename and retain the failed monomorphized LLBC and failed Aeneas translation unchanged. No source or semantics are inferred from this candidate.

The prior proved sampler/execution theorems remain separate Lean artifacts. Aeneas would emit source functions into a new namespace; reuse of prior theorem bodies requires explicit import/bridge work after lead inspection, not an assumption that capture itself reuses them.
