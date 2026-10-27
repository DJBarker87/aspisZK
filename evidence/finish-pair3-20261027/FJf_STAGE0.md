# L142 continuation preflight

Scope: L142 only; new FJf_ modules and task receipts only. Actual branch is
codex/cx-finish-pair3-20261027. All prior FJd_/FJc_ statements are reused,
not reproved. No ELF gate applies to evidence-only work; elf-repro1 owns pins.
No push or merge. No wallet/key operations.

The Rust Weights::new point body is inline at weights.rs:224-227 and the tensor
body at :262-267; neither is a callable library function. An external crate
cannot call one iteration unchanged. Copying those statements would not meet
the requested library-call identity. Adding a callable step would refactor
shipped code outside cfg(kani), which is excluded. We therefore use the P6
route: prove the installed Aeneas body directly, whose .body is callable.
No Kani equality is imported into Lean as an axiom or silently assumed.

Before statement: Rc10_Top.deployed and FIr_Top.deployed, with native L142
and F3Y_G_L142 retained. Exact source hashes are in FJf_baseline.json.
Initial ledger counts inherited from FJd: Rc10 actual83T/12P/13G, combined
89T/16P/13G; FIr actual83T/17P/13G, combined89T/22P/13G.
Non-vacuity is the unchanged conditional FIr_Nonvacuity.composed; no new
unconditional satisfying instance is claimed.
