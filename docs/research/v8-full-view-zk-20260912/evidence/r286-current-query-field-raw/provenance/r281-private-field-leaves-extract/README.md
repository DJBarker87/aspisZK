# R281 isolated QM31 field leaf extraction

R281 is a fresh cached optimized Charon extraction with only these two start roots:

- `aspis_core::field::QM31::neg`
- `aspis_core::field::QM31::mul_m31`

It reuses R280's verified frozen source/manifest/lock hashes, includes (`core::option`, `aspis_core::field`), release command, rustflags loaded from the cached release fingerprint, and systemd limits (`MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`). It uses a new remote directory/unit and R281 output name, with launch campaign Git revision `380c7d46c9719dcfcab601fac2607861d47dee02`; the frozen remote source root has no Git metadata, so source hashes identify the frozen snapshot.

The extracted LLBC has `has_errors=false`. The initial strict local-flag preflight is preserved in `rejected-preflight-check.json`; it failed because Charon marks the selected functions `is_local=false`. Exact artifact inspection confirms Fun0 is `QM31::neg` at `field.rs:874` and Fun1 is `QM31::mul_m31` at `field.rs:927`; both have `Structured` bodies and the expected QM31 receiver type. The field file is part of the frozen `aspis_core` dependency, so the lead accepted these two exact external-crate bodies for further structural review. `root-body-inspection.json` and the updated `acceptance.json` record this fact without a source-semantic claim. No extraction was retried, and no LLBC translation, Lean compilation, or tests were run. R280 remains untouched; its recorded `has_errors=true` Zip transformation diagnostic is not used as an input here.

Extraction: Charon exit 0, wall time 13.33 s, peak RSS 610,952 KiB, swaps 0. Dedicated systemd unit `aspis-r281-private-field-leaves-extract`; limits `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Launch campaign revision: `380c7d46c9719dcfcab601fac2607861d47dee02`. LLBC SHA-256: `6ffca95bc433f10b0b01db769cdb76c9f99421c0d7c3cfb7b4644af2e33b3f01`.
