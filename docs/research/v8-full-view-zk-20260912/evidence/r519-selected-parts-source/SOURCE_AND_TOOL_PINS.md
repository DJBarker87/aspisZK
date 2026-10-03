# R519 selected parts source and tool pins

- Source capture: R508 selected prepare, captured LLBC original SHA-256 `600705e63cb7ba718e09a11e2da257c2fccf097173bfea00f294446265d32bc8`; exact bytes are archived as gzip under `campaign-record/` and decompression is verified in `ARCHIVE_MANIFEST.json`.
- Captured source revision: `4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35`; original frozen R117 source revision: `6677d5f1310ff7373301fbd79f186278f772e68a`. The pinned source hashes and runner/capture command are included in the archived R508 receipt and launch files.
- The embedded `shared_gamma.rs` matches source SHA-256 `75c26014c9900221445c14536d966f3d9267b53b331709099afda6374bf72552`. The remote pinned `aspis-core/src/field.rs` source was read-only hashed as `639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499`.
- Aeneas binary: R497 candidate SHA-256 `85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b`.
- Lean build: Lean 4.32.0 in the pinned cached workspace; Types/Funs jobs used `-j1 -M4500`, each with systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Full commands, source SHAs, logs, receipts and axiom output are retained.

The formal coverage is the generated `shared_gamma::parts` helper and its selected generated field-add closure after explicit captured-literal operand and unused-global export-group normalization. It does not establish the entire Rust callback/native caller correspondence, privacy, or soundness.
